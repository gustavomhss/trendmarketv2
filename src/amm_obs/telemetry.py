"""Deterministic helpers to emulate TrendMarket AMM observability.

This module provides two main entry-points used across the CRD-8 waves:

* :class:`AMMObservability` — in-memory generator that records metrics,
  traces and structured logs for core AMM operations.  The generator is
  deterministic (seeded) so evidence can be reproduced locally and in CI.
* :func:`run_dev_server` — lightweight HTTP server that exposes the
  generated Prometheus histogram (`/metrics`), a basic health endpoint and
  synthetic routes (``/swap``/``/add_liquidity``/``/remove_liquidity``/
  ``/pricing``/``/cdc_consume``) useful for manual smoke tests.

The design deliberately avoids third-party dependencies so it runs in the
minimal runner image used by the epic orchestration.
"""
from __future__ import annotations

import json
import os
import random
import threading
from dataclasses import dataclass
from datetime import datetime, timezone
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from typing import Dict, Iterable, List, Optional
from urllib.parse import urlparse

# --- Metric configuration ----------------------------------------------------

HISTOGRAM_BUCKETS: List[float] = [
    0.005,
    0.01,
    0.02,
    0.03,
    0.05,
    0.075,
    0.1,
    0.15,
    0.2,
    0.3,
    0.5,
    0.75,
    1.0,
    1.5,
    2.0,
    3.0,
    5.0,
]

# Curated latency profiles for each core AMM operation.  The numbers were
# chosen to keep p95(swap) < 60ms (SLO) while still exercising histogram
# buckets across a broad range.
DEFAULT_OPERATION_PROFILE: Dict[str, List[float]] = {
    "swap": [0.012, 0.018, 0.026, 0.035, 0.041, 0.052],
    "add_liquidity": [0.028, 0.032, 0.037, 0.041],
    "remove_liquidity": [0.031, 0.036, 0.043, 0.049],
    "pricing": [0.007, 0.009, 0.013, 0.017, 0.02],
    "cdc_consume": [0.062, 0.073, 0.081, 0.089],
}

# --- Helper utilities --------------------------------------------------------


def _utc_now() -> datetime:
    return datetime.now(timezone.utc)


def _format_ts(ts: datetime) -> str:
    return ts.isoformat().replace("+00:00", "Z")


def _trace_id(rng: random.Random) -> str:
    return f"{rng.getrandbits(128):032x}"


def _span_id(rng: random.Random) -> str:
    return f"{rng.getrandbits(64):016x}"


def _round(value: float) -> float:
    return round(value, 6)


@dataclass
class _Event:
    op: str
    latency_seconds: float
    trace_id: str
    span_id: str
    start_time: str
    status: str
    attributes: Dict[str, str]
    route: Optional[str] = None


class AMMObservability:
    """Collects deterministic metrics, traces and logs for AMM operations."""

    def __init__(
        self,
        *,
        env: str = "dev",
        service: str = "trendmarket-amm",
        version: str = "v0.1.0",
        seed: int = 202402,
        operation_profile: Optional[Dict[str, Iterable[float]]] = None,
    ) -> None:
        self.env = env
        self.service = service
        self.version = version
        profile = operation_profile or DEFAULT_OPERATION_PROFILE
        self._profile: Dict[str, List[float]] = {
            op: list(values) for op, values in profile.items()
        }
        self._rng = random.Random(seed)
        self._lock = threading.RLock()
        self._latency_records: Dict[str, List[float]] = {
            op: [] for op in self._profile
        }
        self._events: List[_Event] = []
        self._exemplars: Dict[str, Dict[str, object]] = {}
        self._profile_index: Dict[str, int] = {op: 0 for op in self._profile}

    # ------------------------------------------------------------------ events
    def record_operation(
        self,
        op: str,
        latency_seconds: float,
        *,
        status: str = "OK",
        route: Optional[str] = None,
        extra_attributes: Optional[Dict[str, str]] = None,
    ) -> _Event:
        if op not in self._profile:
            raise ValueError(f"unknown operation: {op}")
        with self._lock:
            latency = _round(float(latency_seconds))
            ts = _utc_now()
            trace_id = _trace_id(self._rng)
            span_id = _span_id(self._rng)
            attributes = {
                "service.name": self.service,
                "service.version": self.version,
                "net.peer.env": self.env,
                "amm.operation": op,
            }
            if route:
                attributes["http.route"] = route
            if extra_attributes:
                attributes.update(extra_attributes)

            event = _Event(
                op=op,
                latency_seconds=latency,
                trace_id=trace_id,
                span_id=span_id,
                start_time=_format_ts(ts),
                status=status,
                attributes=attributes,
                route=route,
            )
            self._events.append(event)
            self._latency_records.setdefault(op, []).append(latency)
            # Capture the first observation per operation as exemplar to link
            # metrics with traces/logs deterministically.
            if op not in self._exemplars:
                self._exemplars[op] = {
                    "trace_id": trace_id,
                    "span_id": span_id,
                    "latency_seconds": latency,
                    "start_time": event.start_time,
                }
            return event

    def simulate_operation(self, op: str) -> _Event:
        """Record one synthetic invocation of ``op`` using the profile."""
        latency = self._next_latency(op)
        return self.record_operation(op, latency, route=f"/{op}")

    def simulate_unit_load(self) -> None:
        """Populate deterministic evidence for all operations."""
        for op, latencies in self._profile.items():
            for latency in latencies:
                self.record_operation(op, latency, route=f"/{op}")

    # ----------------------------------------------------------------- exports
    def metrics_snapshot(self) -> Dict[str, object]:
        ops_snapshot = {}
        for op, values in self._latency_records.items():
            if not values:
                continue
            ops_snapshot[op] = {
                "count": len(values),
                "sum": _round(sum(values)),
                "min": _round(min(values)),
                "max": _round(max(values)),
                "avg": _round(sum(values) / len(values)),
                "p50": _round(self._quantile(values, 0.50)),
                "p75": _round(self._quantile(values, 0.75)),
                "p95": _round(self._quantile(values, 0.95)),
                "buckets": self._bucket_counts(values),
            }
        return {
            "metric": "amm_op_latency_seconds",
            "unit": "seconds",
            "labels": {
                "env": self.env,
                "service": self.service,
                "version": self.version,
            },
            "operations": ops_snapshot,
            "exemplars": self._exemplars,
        }

    def export_prometheus(self) -> str:
        lines = [
            "# HELP amm_op_latency_seconds AMM operation latency",
            "# TYPE amm_op_latency_seconds histogram",
            "# UNIT amm_op_latency_seconds seconds",
        ]
        for op, values in self._latency_records.items():
            if not values:
                continue
            cumulative = self._cumulative_buckets(values)
            for bucket, count in cumulative.items():
                lines.append(
                    f"amm_op_latency_seconds_bucket{{{self._label_pairs(op, {'le': bucket})}}} {count}"
                )
            total = len(values)
            total_sum = _round(sum(values))
            lines.append(
                f"amm_op_latency_seconds_sum{{{self._label_pairs(op)}}} {total_sum}"
            )
            lines.append(
                f"amm_op_latency_seconds_count{{{self._label_pairs(op)}}} {total}"
            )
        return "\n".join(lines) + "\n"

    def serialize(self) -> Dict[str, object]:
        return {
            "meta": {
                "env": self.env,
                "service": self.service,
                "version": self.version,
                "generated_at": _format_ts(_utc_now()),
            },
            "spans": [
                {
                    "trace_id": e.trace_id,
                    "span_id": e.span_id,
                    "name": f"amm.{e.op}",
                    "op": e.op,
                    "latency_seconds": e.latency_seconds,
                    "status": e.status,
                    "start_time": e.start_time,
                    "attributes": e.attributes,
                }
                for e in self._events
            ],
            "logs": [
                {
                    "trace_id": e.trace_id,
                    "span_id": e.span_id,
                    "timestamp": e.start_time,
                    "level": "INFO" if e.status == "OK" else "ERROR",
                    "message": f"{e.op} completed",
                    "fields": {
                        "op": e.op,
                        "latency_seconds": e.latency_seconds,
                        "status": e.status,
                    },
                }
                for e in self._events
            ],
        }

    def write_prometheus_file(self, path: Path) -> None:
        path.write_text(self.export_prometheus(), encoding="utf-8")

    def write_metrics_unit(self, path: Path) -> None:
        path.write_text(
            json.dumps(self.metrics_snapshot(), indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )

    def write_state(self, path: Path) -> None:
        path.write_text(
            json.dumps(self.serialize(), indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )

    # ---------------------------------------------------------------- private
    def _next_latency(self, op: str) -> float:
        profile = self._profile.get(op)
        if not profile:
            # Should not happen because record_operation guards `op`.
            return _round(0.05 + self._rng.random() * 0.01)
        idx = self._profile_index[op]
        latency = float(profile[idx % len(profile)])
        self._profile_index[op] = (idx + 1) % len(profile)
        return _round(latency)

    @staticmethod
    def _quantile(values: List[float], q: float) -> float:
        if not values:
            return 0.0
        ordered = sorted(values)
        if len(ordered) == 1:
            return ordered[0]
        pos = (len(ordered) - 1) * q
        lower = int(pos)
        upper = min(lower + 1, len(ordered) - 1)
        weight = pos - lower
        return ordered[lower] * (1 - weight) + ordered[upper] * weight

    @staticmethod
    def _bucket_counts(values: List[float]) -> Dict[str, int]:
        counts: Dict[str, int] = {}
        for bucket in HISTOGRAM_BUCKETS:
            counts[str(bucket)] = sum(1 for v in values if v <= bucket)
        counts["+Inf"] = len(values)
        return counts

    @staticmethod
    def _cumulative_buckets(values: List[float]) -> Dict[str, int]:
        cumulative: Dict[str, int] = {}
        for bucket in HISTOGRAM_BUCKETS:
            cumulative[str(bucket)] = sum(1 for v in values if v <= bucket)
        cumulative["+Inf"] = len(values)
        return cumulative

    def _label_pairs(self, op: str, extra: Optional[Dict[str, object]] = None) -> str:
        labels = [
            ("op", op),
            ("env", self.env),
            ("service", self.service),
            ("version", self.version),
        ]
        if extra:
            for key, value in extra.items():
                labels.append((key, value))
        return ",".join(f'{key}="{value}"' for key, value in labels)


# --- Lightweight dev server --------------------------------------------------


def run_dev_server(
    *,
    host: str = "0.0.0.0",
    port: int = 8888,
    env: Optional[str] = None,
    service: Optional[str] = None,
    version: Optional[str] = None,
) -> None:
    """Run a blocking HTTP server for local smoke tests."""

    telemetry = AMMObservability(
        env=env or os.getenv("OBS_ENV", "dev"),
        service=service or os.getenv("OBS_SERVICE", "trendmarket-amm"),
        version=version or os.getenv("OBS_VERSION", "v0.1.0"),
    )
    telemetry.simulate_unit_load()

    class Handler(BaseHTTPRequestHandler):
        def do_GET(self) -> None:  # noqa: N802 - interface contract
            parsed = urlparse(self.path)
            path = parsed.path.rstrip("/") or "/"
            if path == "/health":
                self._write_json({"status": "ok", "operations": list(telemetry._profile.keys())})
                return
            if path == "/metrics":
                body = telemetry.export_prometheus().encode("utf-8")
                self.send_response(200)
                self.send_header("Content-Type", "text/plain; version=0.0.4")
                self.send_header("Content-Length", str(len(body)))
                self.end_headers()
                self.wfile.write(body)
                return
            op = path.lstrip("/")
            if op in telemetry._profile:
                event = telemetry.simulate_operation(op)
                self._write_json(
                    {
                        "op": event.op,
                        "trace_id": event.trace_id,
                        "span_id": event.span_id,
                        "latency_seconds": event.latency_seconds,
                        "start_time": event.start_time,
                        "status": event.status,
                    }
                )
                return
            self.send_error(404, "unknown route")

        def log_message(self, _format: str, *_args: object) -> None:  # noqa: D401
            """Silence default HTTP server logging to keep CI output clean."""
            return

        def _write_json(self, payload: Dict[str, object]) -> None:
            body = json.dumps(payload).encode("utf-8")
            self.send_response(200)
            self.send_header("Content-Type", "application/json")
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)

    server = ThreadingHTTPServer((host, port), Handler)
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass
    finally:
        server.server_close()


__all__ = ["AMMObservability", "run_dev_server"]


if __name__ == "__main__":
    run_dev_server()
