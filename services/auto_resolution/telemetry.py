"""Telemetry helpers for the auto-resolution service."""

from __future__ import annotations

from contextlib import contextmanager
from typing import Any, Dict, Iterator, Optional
import os


try:  # pragma: no cover - optional dependency
    from opentelemetry import trace as ot_trace
    from opentelemetry.metrics import get_meter
    from opentelemetry.trace import Status, StatusCode
except Exception:  # pragma: no cover - gracefully degrade without otel
    ot_trace = None
    Status = StatusCode = None

    def get_meter(_name: str) -> None:  # type: ignore[override]
        return None


class _NoOpCounter:
    def add(self, *_: Any, **__: Any) -> None:
        return None


class _NoOpHistogram:
    def record(self, *_: Any, **__: Any) -> None:
        return None


class _NoOpUpDownCounter:
    def add(self, *_: Any, **__: Any) -> None:
        return None


class AutoResolutionTelemetry:
    """Encapsulates the counters, histograms and spans emitted by the resolver."""

    def __init__(self) -> None:
        env = (
            os.getenv("TREND_ENV")
            or os.getenv("DEPLOY_ENV")
            or os.getenv("ENVIRONMENT")
            or "dev"
        )
        self._base_attributes: Dict[str, Any] = {
            "env": env,
            "service_name": "auto-resolution",
        }

        meter = None
        try:  # pragma: no cover - meter acquisition best effort
            meter = get_meter("mbp-auto-resolution") if get_meter else None
        except Exception:
            meter = None

        if meter is None:
            self._latency = _NoOpHistogram()
            self._attempts = _NoOpCounter()
            self._backlog = _NoOpUpDownCounter()
        else:
            try:
                self._latency = meter.create_histogram(
                    "mbp_auto_resolve_latency_ms",
                    unit="ms",
                    description="Latency between request receipt and auto-resolution decision.",
                )
            except Exception:
                self._latency = _NoOpHistogram()

            try:
                self._attempts = meter.create_counter(
                    "mbp_auto_resolve_attempts_total",
                    description="Total auto-resolution attempts broken down by mode and status.",
                )
            except Exception:
                self._attempts = _NoOpCounter()

            try:
                self._backlog = meter.create_up_down_counter(
                    "mbp_auto_resolve_backlog",
                    description="Outstanding disputes pending manual resolution after auto failure.",
                )
            except Exception:
                self._backlog = _NoOpUpDownCounter()

        if ot_trace is not None:  # pragma: no cover - optional dependency
            try:
                self._tracer = ot_trace.get_tracer("mbp-auto-resolution")
            except Exception:
                self._tracer = None
        else:
            self._tracer = None

    def record_success(
        self,
        *,
        mode: str,
        duration_ms: float,
        outcome: str,
        truth_source_used: bool,
    ) -> None:
        attributes = self._attributes(
            {
                "mode": mode,
                "status": "success",
                "outcome": outcome,
                "truth_source_used": "true" if truth_source_used else "false",
            }
        )
        self._attempts.add(1, attributes=attributes)
        latency_attrs = self._attributes({"mode": mode})
        self._latency.record(duration_ms, attributes=latency_attrs)

    def record_failure(self, *, mode: str, duration_ms: float, reason: str) -> None:
        attributes = self._attributes(
            {"mode": mode, "status": "failure", "reason": reason}
        )
        self._attempts.add(1, attributes=attributes)
        latency_attrs = self._attributes({"mode": mode, "status": "failure"})
        self._latency.record(duration_ms, attributes=latency_attrs)

    def adjust_backlog(self, *, delta: int, reason: str) -> None:
        attributes = self._attributes({"reason": reason})
        self._backlog.add(delta, attributes=attributes)

    @contextmanager
    def span(
        self, name: str, *, attributes: Optional[Dict[str, Any]] = None
    ) -> Iterator[Any]:
        if self._tracer is None:
            yield None
            return

        span_attributes = self._attributes(attributes or {})
        with self._tracer.start_as_current_span(
            name, attributes=span_attributes
        ) as span:
            yield span

    def span_record_error(self, span: Any, exc: Exception) -> None:
        if span is None:
            return
        if hasattr(span, "record_exception"):
            span.record_exception(exc)
        if (
            Status is not None
            and StatusCode is not None
            and hasattr(span, "set_status")
        ):
            span.set_status(Status(StatusCode.ERROR, str(exc)))

    def _attributes(self, extra: Dict[str, Any]) -> Dict[str, Any]:
        merged = dict(self._base_attributes)
        merged.update(extra)
        return merged


telemetry = AutoResolutionTelemetry()


__all__ = ["AutoResolutionTelemetry", "telemetry"]
