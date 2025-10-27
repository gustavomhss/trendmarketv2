"""Deterministic observability fixtures for the TrendMarket AMM."""

from __future__ import annotations

import json
import os
import random
import threading
from dataclasses import dataclass
from datetime import datetime, timezone
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Sequence, Set, Tuple
from urllib.parse import urlparse

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

SYNTHETIC_BUCKETS: List[float] = [0.001, 0.002, 0.003, 0.005, 0.01, 0.02]

DEFAULT_OPERATION_PROFILE: Dict[str, Sequence[float]] = {
    "swap": [0.012, 0.018, 0.026, 0.035, 0.041, 0.052],
    "add_liquidity": [0.028, 0.032, 0.037, 0.041],
    "remove_liquidity": [0.031, 0.036, 0.043, 0.049],
    "pricing": [0.007, 0.009, 0.013, 0.017, 0.02],
    "cdc_consume": [0.062, 0.073, 0.081, 0.089],
}

DEFAULT_DATA_FRESHNESS = [
    {"source": "oracle", "domain": "pricing", "seconds": 2.4},
    {"source": "orderbook", "domain": "trading", "seconds": 1.6},
    {"source": "liquidity_feed", "domain": "inventory", "seconds": 3.1},
]

DEFAULT_CDC_LAG = [
    {"stream": "orders", "partition": "0", "seconds": 4.2},
    {"stream": "orders", "partition": "1", "seconds": 5.1},
    {"stream": "settlements", "partition": "0", "seconds": 7.8},
]

DEFAULT_DRIFT_SCORE = [
    {"feature": "price_psi", "score": 0.12},
    {"feature": "volume_psi", "score": 0.18},
    {"feature": "spread_kl", "score": 0.07},
]

HOOK_CATALOG: Tuple[str, ...] = (
    "hook_pre_trade",
    "hook_risk_checks",
    "hook_settlement_dispatch",
    "hook_cdc_sync",
)

HOOK_EXECUTIONS_BY_OPERATION: Dict[str, Sequence[Tuple[str, str]]] = {
    "swap": [("hook_pre_trade", "success"), ("hook_risk_checks", "success")],
    "add_liquidity": [
        ("hook_pre_trade", "success"),
        ("hook_settlement_dispatch", "success"),
    ],
    "remove_liquidity": [
        ("hook_pre_trade", "success"),
        ("hook_settlement_dispatch", "success"),
    ],
    "pricing": [("hook_risk_checks", "success")],
    "cdc_consume": [("hook_cdc_sync", "success")],
}

_LABEL_ORDER: Dict[str, Tuple[str, ...]] = {
    "data_freshness_seconds": ("source", "domain", "service", "env"),
    "cdc_lag_seconds": ("stream", "partition", "service", "env"),
    "drift_score": ("feature", "service", "env"),
    "hook_executions_total": ("hook_id", "status", "env"),
    "hook_coverage_ratio": ("env",),
    "synthetic_requests_total": ("route", "service", "env"),
    "synthetic_latency_seconds": ("route", "service", "env"),
    "synthetic_ok_ratio": ("route", "service", "env"),
}

CARDINALITY_BUDGET: Dict[str, Dict[str, float]] = {
    "amm_op_latency_seconds_bucket": {"budget": 400.0},
    "data_freshness_seconds": {"budget": 180.0},
    "cdc_lag_seconds": {"budget": 320.0},
    "drift_score": {"budget": 80.0},
    "hook_coverage_ratio": {"budget": 10.0},
    "hook_executions_total": {"budget": 200.0},
    "synthetic_latency_seconds_bucket": {"budget": 60.0},
    "synthetic_requests_total": {"budget": 20.0},
    "synthetic_ok_ratio": {"budget": 20.0},
}

SCRAPE_INTERVAL_SECONDS = 15
RETENTION_DAYS = 30
PRICE_PER_MILLION_SAMPLES = 0.30
_SAMPLES_PER_DAY = 86400 / SCRAPE_INTERVAL_SECONDS

_REPO_ROOT = Path(__file__).resolve().parents[2]
_LOG_DENYLIST_PATH = _REPO_ROOT / "ops" / "security" / "log_denylist.json"


def _load_log_policies() -> Tuple[Set[str], Tuple[str, ...]]:
    try:
        payload = json.loads(_LOG_DENYLIST_PATH.read_text(encoding="utf-8"))
    except FileNotFoundError:
        return set(), tuple()
    keys = {
        entry.strip().lower()
        for entry in payload.get("deny_keys", [])
        if isinstance(entry, str)
    }
    substrings = tuple(
        entry.strip().lower()
        for entry in payload.get("deny_substrings", [])
        if isinstance(entry, str)
    )
    return keys, substrings


_DENY_KEYS, _DENY_SUBSTRINGS = _load_log_policies()


def _sanitize_value(value: object) -> object:
    if isinstance(value, str):
        lower = value.lower()
        if any(token in lower for token in _DENY_SUBSTRINGS):
            return "[REDACTED]"
    return value


def _sanitize_log_fields(fields: Dict[str, object]) -> Dict[str, object]:
    sanitized: Dict[str, object] = {}
    for key, value in fields.items():
        if key.lower() in _DENY_KEYS:
            continue
        sanitized[key] = _sanitize_value(value)
    return sanitized


def _sanitize_message(message: str) -> str:
    if any(token in message.lower() for token in _DENY_SUBSTRINGS):
        return "[REDACTED]"
    return message


def _utc_now() -> datetime:
    return datetime.now(timezone.utc)


def _format_ts(value: datetime) -> str:
    return value.astimezone(timezone.utc).isoformat().replace("+00:00", "Z")


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
        operation_profile: Optional[Dict[str, Sequence[float]]] = None,
        observability_level: Optional[str] = None,
    ) -> None:
        level = (
            observability_level or os.getenv("OBSERVABILITY_LEVEL", "full")
        ).lower()
        if level not in {"off", "min", "full"}:
            raise ValueError("observability_level must be one of {'off','min','full'}")

        self.env = env
        self.service = service
        self.version = version
        self._level = level

        profile = operation_profile or DEFAULT_OPERATION_PROFILE
        self._profile: Dict[str, List[float]] = {
            op: list(values) for op, values in profile.items()
        }
        self._profile_index: Dict[str, int] = {op: 0 for op in self._profile}

        self._rng = random.Random(seed)
        self._lock = threading.RLock()

        self._latency_records: Dict[str, List[float]] = {op: [] for op in self._profile}
        self._events: List[_Event] = []
        self._spans: List[Dict[str, object]] = []
        self._logs: List[Dict[str, object]] = []
        self._exemplars: Dict[str, Dict[str, object]] = {}

        self._data_freshness = self._build_gauge_samples(
            "data_freshness_seconds", DEFAULT_DATA_FRESHNESS, "seconds"
        )
        self._cdc_lag = self._build_gauge_samples(
            "cdc_lag_seconds", DEFAULT_CDC_LAG, "seconds"
        )
        self._drift_scores = self._build_gauge_samples(
            "drift_score", DEFAULT_DRIFT_SCORE, "score"
        )

        self._hook_executions: Dict[Tuple[str, str], int] = {}
        self._executed_hooks: Set[str] = set()
        self._hook_catalog: Tuple[str, ...] = HOOK_CATALOG
        self._hook_coverage = {
            "labels": self._compose_labels("hook_coverage_ratio", {}),
            "value": 0.0,
            "catalog": list(self._hook_catalog),
            "executed": [],
        }

        self._synthetic_counts: Dict[str, int] = {}
        self._synthetic_success: Dict[str, int] = {}
        self._synthetic_latencies: Dict[str, List[float]] = {}

    # ------------------------------------------------------------------ events
    def record_operation(
        self,
        op: str,
        latency_seconds: float,
        *,
        status: str = "OK",
        route: Optional[str] = None,
        synthetic: bool = False,
        extra_attributes: Optional[Dict[str, str]] = None,
    ) -> _Event:
        if op not in self._profile:
            raise ValueError(f"unknown operation: {op}")

        with self._lock:
            latency = _round(float(latency_seconds))
            timestamp = _utc_now()
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
                start_time=_format_ts(timestamp),
                status=status,
                attributes=attributes,
                route=route,
            )
            self._events.append(event)
            self._latency_records.setdefault(op, []).append(latency)
            self._record_hook_activity(op)

            if op not in self._exemplars:
                self._exemplars[op] = {
                    "trace_id": trace_id,
                    "span_id": span_id,
                    "latency_seconds": latency,
                    "start_time": event.start_time,
                }

            if synthetic:
                route_name = (route or f"/{op}").lstrip("/") or op
                self._synthetic_counts[route_name] = (
                    self._synthetic_counts.get(route_name, 0) + 1
                )
                if status.upper() == "OK":
                    self._synthetic_success[route_name] = (
                        self._synthetic_success.get(route_name, 0) + 1
                    )
                self._synthetic_latencies.setdefault(route_name, []).append(latency)

            if self._level != "off":
                span = {
                    "trace_id": trace_id,
                    "span_id": span_id,
                    "op": op,
                    "latency_seconds": latency,
                    "start_time": event.start_time,
                    "status": status,
                    "attributes": dict(attributes),
                }
                log_entry = {
                    "trace_id": trace_id,
                    "span_id": span_id,
                    "timestamp": event.start_time,
                    "level": "INFO" if status == "OK" else "ERROR",
                    "message": _sanitize_message(f"{op} completed"),
                    "fields": _sanitize_log_fields(
                        {"op": op, "latency_seconds": latency, "status": status}
                    ),
                }
                self._spans.append(span)
                self._logs.append(log_entry)

            return event

    def simulate_operation(self, op: str) -> _Event:
        latency = self._next_latency(op)
        return self.record_operation(op, latency, route=f"/{op}", synthetic=True)

    def simulate_unit_load(self) -> None:
        for op, latencies in self._profile.items():
            for latency in latencies:
                self.record_operation(op, latency, route=f"/{op}", synthetic=True)
        self._refresh_hook_coverage()

    # ----------------------------------------------------------------- exports
    def metrics_snapshot(self) -> Dict[str, object]:
        operations: Dict[str, Dict[str, object]] = {}
        for op, values in self._latency_records.items():
            if not values:
                continue
            operations[op] = {
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

        supporting: Dict[str, object] = {
            "data_freshness_seconds": self._samples_to_dict(self._data_freshness),
            "cdc_lag_seconds": self._samples_to_dict(self._cdc_lag),
            "drift_score": self._samples_to_dict(self._drift_scores),
            "hook_executions_total": self._counter_samples(),
            "hook_coverage_ratio": self._hook_coverage_snapshot(),
        }
        synthetic = self._synthetic_snapshot()
        if synthetic:
            supporting["synthetic"] = synthetic

        snapshot = {
            "metric": "amm_op_latency_seconds",
            "unit": "seconds",
            "labels": {
                "env": self.env,
                "service": self.service,
                "version": self.version,
            },
            "operations": operations,
            "exemplars": dict(self._exemplars),
            "supporting": supporting,
            "observability_level": self._level,
            "cardinality": self.cardinality_breakdown(),
        }
        return snapshot

    def export_prometheus(self) -> str:
        lines = [
            "# HELP amm_op_latency_seconds AMM operation latency",
            "# TYPE amm_op_latency_seconds histogram",
            "# UNIT amm_op_latency_seconds seconds",
        ]
        for op, values in self._latency_records.items():
            if not values:
                continue
            cumulative = self._cumulative_buckets(values, HISTOGRAM_BUCKETS)
            for bucket, count in cumulative.items():
                labels = self._label_pairs(op, {"le": bucket})
                lines.append(f"amm_op_latency_seconds_bucket{{{labels}}} {count}")
            total = len(values)
            total_sum = _round(sum(values))
            lines.append(
                f"amm_op_latency_seconds_sum{{{self._label_pairs(op)}}} {total_sum}"
            )
            lines.append(
                f"amm_op_latency_seconds_count{{{self._label_pairs(op)}}} {total}"
            )

        if self._data_freshness:
            lines.extend(
                [
                    "# HELP data_freshness_seconds Data freshness lag",
                    "# TYPE data_freshness_seconds gauge",
                    "# UNIT data_freshness_seconds seconds",
                ]
            )
            for sample in self._data_freshness:
                labels = self._format_metric_labels(
                    "data_freshness_seconds", sample["labels"]
                )
                lines.append(f"data_freshness_seconds{{{labels}}} {sample['value']}")

        if self._cdc_lag:
            lines.extend(
                [
                    "# HELP cdc_lag_seconds CDC consumer lag",
                    "# TYPE cdc_lag_seconds gauge",
                    "# UNIT cdc_lag_seconds seconds",
                ]
            )
            for sample in self._cdc_lag:
                labels = self._format_metric_labels("cdc_lag_seconds", sample["labels"])
                lines.append(f"cdc_lag_seconds{{{labels}}} {sample['value']}")

        if self._drift_scores:
            lines.extend(
                [
                    "# HELP drift_score Feature drift score (PSI/KL)",
                    "# TYPE drift_score gauge",
                ]
            )
            for sample in self._drift_scores:
                labels = self._format_metric_labels("drift_score", sample["labels"])
                lines.append(f"drift_score{{{labels}}} {sample['value']}")

        if self._hook_executions:
            lines.extend(
                [
                    "# HELP hook_executions_total Hook executions grouped by outcome",
                    "# TYPE hook_executions_total counter",
                ]
            )
            for sample in self._counter_samples():
                labels = self._format_metric_labels(
                    "hook_executions_total", sample["labels"]
                )
                lines.append(f"hook_executions_total{{{labels}}} {sample['value']}")

        if self._hook_coverage:
            lines.extend(
                [
                    "# HELP hook_coverage_ratio Hook coverage ratio",
                    "# TYPE hook_coverage_ratio gauge",
                ]
            )
            labels = self._format_metric_labels(
                "hook_coverage_ratio", self._hook_coverage["labels"]
            )
            lines.append(
                f"hook_coverage_ratio{{{labels}}} {self._hook_coverage['value']}"
            )

        if self._synthetic_counts:
            lines.extend(
                [
                    "# HELP synthetic_requests_total Synthetic probe executions",
                    "# TYPE synthetic_requests_total counter",
                ]
            )
            for route, count in sorted(self._synthetic_counts.items()):
                labels = self._synthetic_label_pairs(route)
                lines.append(f"synthetic_requests_total{{{labels}}} {count}")

            lines.extend(
                [
                    "# HELP synthetic_latency_seconds Synthetic probe latency",
                    "# TYPE synthetic_latency_seconds histogram",
                    "# UNIT synthetic_latency_seconds seconds",
                ]
            )
            for route, latencies in sorted(self._synthetic_latencies.items()):
                cumulative = self._cumulative_buckets(latencies, SYNTHETIC_BUCKETS)
                for bucket, count in cumulative.items():
                    labels = self._synthetic_label_pairs(route, {"le": bucket})
                    lines.append(
                        f"synthetic_latency_seconds_bucket{{{labels}}} {count}"
                    )
                total = len(latencies)
                total_sum = _round(sum(latencies))
                labels = self._synthetic_label_pairs(route)
                lines.append(f"synthetic_latency_seconds_sum{{{labels}}} {total_sum}")
                lines.append(f"synthetic_latency_seconds_count{{{labels}}} {total}")

            lines.extend(
                [
                    "# HELP synthetic_ok_ratio Synthetic success ratio",
                    "# TYPE synthetic_ok_ratio gauge",
                ]
            )
            for route, total in sorted(self._synthetic_counts.items()):
                success = self._synthetic_success.get(route, 0)
                ratio = round(success / total, 4) if total else 0.0
                labels = self._synthetic_label_pairs(route)
                lines.append(f"synthetic_ok_ratio{{{labels}}} {ratio}")

        return "\n".join(lines) + "\n"

    def cardinality_breakdown(self) -> Dict[str, object]:
        metrics: Dict[str, Dict[str, object]] = {}

        histogram_series = len(self._profile) * (len(HISTOGRAM_BUCKETS) + 1)
        metrics["amm_op_latency_seconds_bucket"] = {"series": float(histogram_series)}

        metrics["data_freshness_seconds"] = {"series": float(len(self._data_freshness))}
        metrics["cdc_lag_seconds"] = {"series": float(len(self._cdc_lag))}
        metrics["drift_score"] = {"series": float(len(self._drift_scores))}

        hook_exec_series = len(
            {
                (hook, status)
                for hooks in HOOK_EXECUTIONS_BY_OPERATION.values()
                for hook, status in hooks
            }
        )
        metrics["hook_executions_total"] = {"series": float(hook_exec_series)}
        metrics["hook_coverage_ratio"] = {"series": 1.0}

        synthetic_routes = max(
            len(self._synthetic_latencies), len(self._profile)
        ) or len(self._profile)
        metrics["synthetic_latency_seconds_bucket"] = {
            "series": float(synthetic_routes * (len(SYNTHETIC_BUCKETS) + 1))
        }
        synthetic_series = max(len(self._synthetic_counts), synthetic_routes)
        metrics["synthetic_requests_total"] = {"series": float(synthetic_series)}
        metrics["synthetic_ok_ratio"] = {"series": float(synthetic_series)}

        total_cost = 0.0
        max_ratio = 0.0
        worst_metric: Optional[str] = None

        for metric, payload in metrics.items():
            series = payload["series"]
            budget = CARDINALITY_BUDGET.get(metric, {}).get("budget")
            if budget:
                ratio = round(series / budget, 4)
                payload["budget"] = budget
                payload["ratio"] = ratio
                if ratio > max_ratio:
                    max_ratio = ratio
                    worst_metric = metric
            cost = round(
                series
                * _SAMPLES_PER_DAY
                * RETENTION_DAYS
                * PRICE_PER_MILLION_SAMPLES
                / 1e6,
                2,
            )
            payload["est_usd_month"] = cost
            total_cost += cost

        return {
            "metrics": metrics,
            "price_per_million_samples": PRICE_PER_MILLION_SAMPLES,
            "retention_days": RETENTION_DAYS,
            "scrape_interval_seconds": SCRAPE_INTERVAL_SECONDS,
            "total_estimated_usd_month": round(total_cost, 2),
            "max_ratio": max_ratio,
            "max_ratio_metric": worst_metric,
        }

    def serialize(self) -> Dict[str, object]:
        return {
            "meta": {
                "env": self.env,
                "service": self.service,
                "version": self.version,
                "observability_level": self._level,
                "generated_at": _format_ts(_utc_now()),
            },
            "spans": list(self._spans),
            "logs": list(self._logs),
            "metrics": {
                "amm_op_latency_seconds": self.metrics_snapshot(),
                "data_freshness_seconds": self._samples_to_dict(self._data_freshness),
                "cdc_lag_seconds": self._samples_to_dict(self._cdc_lag),
                "drift_score": self._samples_to_dict(self._drift_scores),
                "hook_executions_total": self._counter_samples(),
                "hook_coverage_ratio": self._hook_coverage_snapshot(),
            },
        }

    def write_prometheus_file(self, path: Path) -> None:
        path.write_text(self.export_prometheus(), encoding="utf-8")

    def write_metrics_unit(self, path: Path) -> None:
        payload = self.metrics_snapshot()
        path.write_text(
            json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8"
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
            return _round(0.05 + self._rng.random() * 0.01)
        idx = self._profile_index[op]
        latency = float(profile[idx % len(profile)])
        self._profile_index[op] = (idx + 1) % len(profile)
        return _round(latency)

    @staticmethod
    def _quantile(values: Sequence[float], q: float) -> float:
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
    def _bucket_counts(values: Sequence[float]) -> Dict[str, int]:
        counts: Dict[str, int] = {}
        for bucket in HISTOGRAM_BUCKETS:
            counts[str(bucket)] = sum(1 for value in values if value <= bucket)
        counts["+Inf"] = len(values)
        return counts

    @staticmethod
    def _cumulative_buckets(
        values: Sequence[float], buckets: Sequence[float]
    ) -> Dict[str, int]:
        cumulative: Dict[str, int] = {}
        for bucket in buckets:
            cumulative[str(bucket)] = sum(1 for value in values if value <= bucket)
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
            labels.extend(extra.items())
        return ",".join(f'{key}="{value}"' for key, value in labels)

    def _synthetic_label_pairs(
        self, route: str, extra: Optional[Dict[str, object]] = None
    ) -> str:
        labels = [("route", route), ("env", self.env), ("service", self.service)]
        if extra:
            labels.extend(extra.items())
        return ",".join(f'{key}="{value}"' for key, value in labels)

    def _build_gauge_samples(
        self, metric: str, values: Iterable[Dict[str, object]], value_key: str
    ) -> List[Dict[str, object]]:
        samples: List[Dict[str, object]] = []
        for entry in values:
            labels = {
                key: str(entry[key])
                for key in _LABEL_ORDER.get(metric, tuple())
                if key in entry
            }
            if "service" in _LABEL_ORDER.get(metric, tuple()):
                labels.setdefault("service", self.service)
            if "env" in _LABEL_ORDER.get(metric, tuple()):
                labels.setdefault("env", self.env)
            samples.append({"labels": labels, "value": _round(float(entry[value_key]))})
        return samples

    def _compose_labels(self, metric: str, base: Dict[str, str]) -> Dict[str, str]:
        labels: Dict[str, str] = {}
        for key in _LABEL_ORDER.get(metric, tuple()):
            if key == "service":
                labels[key] = self.service
            elif key == "env":
                labels[key] = self.env
            else:
                if key not in base:
                    raise KeyError(f"missing label '{key}' for metric {metric}")
                labels[key] = base[key]
        return labels

    def _format_metric_labels(self, metric: str, labels: Dict[str, str]) -> str:
        order = _LABEL_ORDER.get(metric, tuple())
        if not order:
            return ",".join(f'{key}="{value}"' for key, value in sorted(labels.items()))
        return ",".join(f'{key}="{labels[key]}"' for key in order if key in labels)

    def _record_hook_activity(self, op: str) -> None:
        hooks = HOOK_EXECUTIONS_BY_OPERATION.get(op)
        if not hooks:
            return
        for hook_id, status in hooks:
            key = (hook_id, status)
            self._hook_executions[key] = self._hook_executions.get(key, 0) + 1
            self._executed_hooks.add(hook_id)
        self._refresh_hook_coverage()

    def _refresh_hook_coverage(self) -> None:
        if not self._hook_catalog:
            self._hook_coverage["value"] = 0.0
            return
        ratio = len(self._executed_hooks) / float(len(self._hook_catalog))
        self._hook_coverage["value"] = _round(ratio)
        self._hook_coverage["executed"] = sorted(self._executed_hooks)

    def _synthetic_snapshot(self) -> Dict[str, object]:
        snapshot: Dict[str, object] = {}
        for route, total in sorted(self._synthetic_counts.items()):
            latencies = self._synthetic_latencies.get(route, [])
            success = self._synthetic_success.get(route, 0)
            ratio = round(success / total, 4) if total else None
            snapshot[route] = {
                "count": total,
                "success": success,
                "ok_ratio": ratio,
                "latencies": [_round(value) for value in latencies],
            }
        return snapshot

    @staticmethod
    def _samples_to_dict(
        samples: Iterable[Dict[str, object]],
    ) -> List[Dict[str, object]]:
        return [
            {"labels": dict(sample["labels"]), "value": sample["value"]}
            for sample in samples
        ]

    def _counter_samples(self) -> List[Dict[str, object]]:
        payload: List[Dict[str, object]] = []
        for (hook_id, status), value in sorted(self._hook_executions.items()):
            payload.append(
                {
                    "labels": self._compose_labels(
                        "hook_executions_total", {"hook_id": hook_id, "status": status}
                    ),
                    "value": value,
                }
            )
        return payload

    def _hook_coverage_snapshot(self) -> Dict[str, object]:
        return {
            "labels": dict(self._hook_coverage["labels"]),
            "value": self._hook_coverage["value"],
            "catalog": list(self._hook_catalog),
            "executed": sorted(self._executed_hooks),
        }


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
        observability_level=os.getenv("OBSERVABILITY_LEVEL", "full"),
    )
    telemetry.simulate_unit_load()

    class Handler(BaseHTTPRequestHandler):  # type: ignore[misc]
        def do_GET(self) -> None:  # noqa: N802 (interface contract)
            parsed = urlparse(self.path)
            path = parsed.path.rstrip("/") or "/"
            if path == "/health":
                self._write_json(
                    {"status": "ok", "operations": list(telemetry._profile.keys())}
                )
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
