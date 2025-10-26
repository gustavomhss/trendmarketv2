"""Shared telemetry helpers for Prometheus metrics, OTel spans and event logs."""
from __future__ import annotations

from contextlib import contextmanager
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, Iterator, Optional
import json
import os
import threading
import time

try:  # pragma: no cover - optional dependency
    from prometheus_client import Counter, Gauge, Histogram
except Exception:  # pragma: no cover - gracefully degrade without prometheus
    Counter = Gauge = Histogram = None  # type: ignore

try:  # pragma: no cover - optional dependency
    from opentelemetry import trace as ot_trace
    from opentelemetry.trace import Span
except Exception:  # pragma: no cover - gracefully degrade without otel
    ot_trace = None  # type: ignore
    Span = None  # type: ignore


class _NoopMetric:
    def labels(self, **_: Any) -> "_NoopMetric":
        return self

    def inc(self, *_: Any, **__: Any) -> None:
        return None

    def observe(self, *_: Any, **__: Any) -> None:
        return None

    def set(self, *_: Any, **__: Any) -> None:
        return None

    def add(self, *_: Any, **__: Any) -> None:
        return None


@dataclass(frozen=True)
class TelemetrySettings:
    service_name: str
    env: str = "dev"


class TelemetryManager:
    """Factory for metrics, tracers and event emitters used across services."""

    def __init__(self, settings: TelemetrySettings) -> None:
        self.settings = settings
        self._tracer = None
        if ot_trace is not None:  # pragma: no cover - optional dependency
            try:
                self._tracer = ot_trace.get_tracer(settings.service_name)
            except Exception:  # pragma: no cover - tracer creation failure is non fatal
                self._tracer = None

    # ------------------------------------------------------------------
    # Metric helpers
    # ------------------------------------------------------------------
    def counter(self, name: str, description: str, *, labelnames: tuple[str, ...] = ()) -> Any:
        if Counter is None:  # pragma: no cover - optional dependency missing
            return _NoopMetric()
        return Counter(name, description, labelnames=labelnames)

    def histogram(
        self,
        name: str,
        description: str,
        *,
        buckets: Optional[tuple[float, ...]] = None,
        labelnames: tuple[str, ...] = (),
    ) -> Any:
        if Histogram is None:  # pragma: no cover - optional dependency missing
            return _NoopMetric()
        if buckets is not None:
            return Histogram(name, description, buckets=buckets, labelnames=labelnames)
        return Histogram(name, description, labelnames=labelnames)

    def gauge(self, name: str, description: str, *, labelnames: tuple[str, ...] = ()) -> Any:
        if Gauge is None:  # pragma: no cover - optional dependency missing
            return _NoopMetric()
        return Gauge(name, description, labelnames=labelnames)

    # ------------------------------------------------------------------
    # Spans
    # ------------------------------------------------------------------
    @contextmanager
    def span(self, name: str, *, attributes: Optional[Dict[str, Any]] = None) -> Iterator[Optional[Span]]:
        tracer = self._tracer
        if tracer is None:  # pragma: no cover - no tracer configured
            yield None
            return
        attrs = {"service.name": self.settings.service_name, "service.env": self.settings.env}
        if attributes:
            attrs.update(attributes)
        with tracer.start_as_current_span(name, attributes=attrs) as span:  # pragma: no cover - tracing path
            yield span

    # ------------------------------------------------------------------
    # Events
    # ------------------------------------------------------------------
    def event_log(self, env_var: str, default: Path) -> "EventEmitter":
        path = Path(os.getenv(env_var, str(default)))
        return EventEmitter(path)


class EventEmitter:
    """Write contract-compliant JSON events to an append-only log."""

    def __init__(self, path: Path) -> None:
        self.path = path
        self.path.parent.mkdir(parents=True, exist_ok=True)
        self._lock = threading.Lock()

    def emit(self, event_type: str, payload: Dict[str, Any]) -> None:
        record = {
            "event": event_type,
            "timestamp": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
            "payload": payload,
        }
        with self._lock:
            with self.path.open("a", encoding="utf-8") as handle:
                handle.write(json.dumps(record, sort_keys=True) + "\n")


__all__ = ["TelemetryManager", "TelemetrySettings", "EventEmitter"]
