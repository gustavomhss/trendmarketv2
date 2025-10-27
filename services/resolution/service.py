"""Auto-resolution service with Prometheus and tracing instrumentation."""

from __future__ import annotations

from contextlib import contextmanager
from dataclasses import dataclass
from typing import Dict, Iterable, Iterator, Optional
import os
import time
import uuid

try:  # pragma: no cover - optional dependency
    from prometheus_client import Counter, Gauge, Histogram
except Exception:  # pragma: no cover - defensive fallback when client missing
    Counter = Gauge = Histogram = None  # type: ignore

try:  # pragma: no cover - optional dependency
    from opentelemetry import trace
    from opentelemetry.trace import Span, Status, StatusCode
except Exception:  # pragma: no cover - defensive fallback when client missing
    trace = None  # type: ignore
    Span = Status = StatusCode = None  # type: ignore


OBS_ENV = os.getenv("OBS_ENV", "dev")
_HISTOGRAM_BUCKETS = (
    0.01,
    0.025,
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
)

if Histogram is not None:
    _DECISION_LATENCY = Histogram(
        "mbp_auto_resolve_eval_duration_seconds",
        "Latency of auto-resolution evaluations.",
        labelnames=("truth_source", "env"),
        buckets=_HISTOGRAM_BUCKETS,
    )
else:  # pragma: no cover - fallback when Prometheus client missing
    _DECISION_LATENCY = None

if Counter is not None:
    _DECISIONS_TOTAL = Counter(
        "mbp_auto_resolve_decisions_total",
        "Total auto-resolution decisions processed.",
        labelnames=("truth_source", "outcome", "env"),
    )
    _SUCCESS_TOTAL = Counter(
        "mbp_auto_resolve_success_total",
        "Successful auto-resolution decisions.",
        labelnames=("truth_source", "env"),
    )
else:  # pragma: no cover - fallback when Prometheus client missing
    _DECISIONS_TOTAL = None
    _SUCCESS_TOTAL = None

if Gauge is not None:
    _BACKLOG_GAUGE = Gauge(
        "mbp_auto_resolve_backlog",
        "Auto-resolution backlog size per truth source.",
        labelnames=("truth_source", "env"),
    )
else:  # pragma: no cover - fallback when Prometheus client missing
    _BACKLOG_GAUGE = None

if trace is not None:  # pragma: no cover - optional dependency
    _TRACER = trace.get_tracer("trendmarketv2.services.auto_resolver")
else:  # pragma: no cover
    _TRACER = None


@dataclass
class PendingDecision:
    """Represents a decision waiting for quorum/manual review."""

    decision_id: str
    truth_source: str
    quorum: bool
    payload: Dict[str, object]
    enqueued_at: float
    trace_id: str


@dataclass
class ResolutionRecord:
    """Represents the outcome for a resolved decision."""

    decision_id: str
    truth_source: str
    outcome: str
    resolved_at: float
    latency_ms: float
    trace_id: str
    payload: Dict[str, object]


class DecisionConflictError(RuntimeError):
    """Raised when attempting to resolve an already processed decision."""


@contextmanager
def _span(name: str, **attributes: object) -> Iterator[Optional[Span]]:
    if _TRACER is None:  # pragma: no cover - tracing disabled
        yield None
        return
    with _TRACER.start_as_current_span(name) as span:  # pragma: no cover - tracing
        for key, value in attributes.items():
            span.set_attribute(f"auto_resolve.{key}", value)
        yield span


def _observe_metrics(
    truth_source: str,
    outcome: str,
    duration_seconds: float,
    backlog_for_source: int,
    total_backlog: int,
    *,
    count_decision: bool,
) -> None:
    if _DECISION_LATENCY is not None:
        _DECISION_LATENCY.labels(truth_source=truth_source, env=OBS_ENV).observe(
            duration_seconds
        )
    if _BACKLOG_GAUGE is not None:
        _BACKLOG_GAUGE.labels(truth_source=truth_source, env=OBS_ENV).set(
            backlog_for_source
        )
        _BACKLOG_GAUGE.labels(truth_source="__total__", env=OBS_ENV).set(total_backlog)
    if not count_decision:
        return
    if _DECISIONS_TOTAL is not None:
        _DECISIONS_TOTAL.labels(
            truth_source=truth_source,
            outcome=outcome,
            env=OBS_ENV,
        ).inc()
    if outcome == "applied" and _SUCCESS_TOTAL is not None:
        _SUCCESS_TOTAL.labels(truth_source=truth_source, env=OBS_ENV).inc()


class AutoResolverService:
    """In-memory auto-resolution engine instrumented for observability."""

    def __init__(self) -> None:
        self._pending: Dict[str, PendingDecision] = {}
        self._resolved: Dict[str, ResolutionRecord] = {}

    # ------------------------------------------------------------------
    # Public API
    # ------------------------------------------------------------------
    def apply_decision(
        self,
        *,
        schema_version: int,
        decision_id: str,
        truth_source: str,
        quorum: bool,
        payload: Optional[Dict[str, object]] = None,
    ) -> Dict[str, object]:
        """Apply a decision emitted by the auto-resolver."""

        if schema_version != 1:
            raise ValueError(f"Unsupported schema version: {schema_version}")

        payload_copy = dict(payload or {})
        started = time.perf_counter()
        trace_id = uuid.uuid4().hex

        with _span(
            "auto_resolve.apply",
            decision_id=decision_id,
            truth_source=truth_source,
            quorum=quorum,
        ) as span:
            if decision_id in self._resolved or decision_id in self._pending:
                duration = time.perf_counter() - started
                _observe_metrics(
                    truth_source,
                    "conflict",
                    duration,
                    self.backlog_for_source(truth_source),
                    self.backlog_total,
                    count_decision=True,
                )
                if span is not None:
                    span.set_attribute("auto_resolve.outcome", "conflict")
                    if StatusCode is not None and Status is not None:
                        span.set_status(Status(StatusCode.ERROR, "conflict"))
                    span.record_exception(DecisionConflictError(decision_id))
                raise DecisionConflictError(
                    f"Decision '{decision_id}' already processed"
                )

            if quorum:
                outcome = "applied"
                resolved_at = time.time()
                latency_ms = (time.perf_counter() - started) * 1000
                record = ResolutionRecord(
                    decision_id=decision_id,
                    truth_source=truth_source,
                    outcome=outcome,
                    resolved_at=resolved_at,
                    latency_ms=latency_ms,
                    trace_id=trace_id,
                    payload=payload_copy,
                )
                self._resolved[decision_id] = record
                if decision_id in self._pending:
                    del self._pending[decision_id]
            else:
                outcome = "queued"
                self._pending[decision_id] = PendingDecision(
                    decision_id=decision_id,
                    truth_source=truth_source,
                    quorum=quorum,
                    payload=payload_copy,
                    enqueued_at=time.time(),
                    trace_id=trace_id,
                )

            duration = time.perf_counter() - started
            _observe_metrics(
                truth_source,
                outcome,
                duration,
                self.backlog_for_source(truth_source),
                self.backlog_total,
                count_decision=quorum,
            )
            if span is not None:
                span.set_attribute("auto_resolve.outcome", outcome)
                span.set_attribute("auto_resolve.latency_ms", duration * 1000)
                span.set_attribute("auto_resolve.backlog", self.backlog_total)

        return {"decision_id": decision_id, "outcome": outcome, "trace_id": trace_id}

    def finalize(
        self,
        decision_id: str,
        *,
        accepted: bool,
        reason: Optional[str] = None,
    ) -> ResolutionRecord:
        """Finalize a previously queued decision."""

        pending = self._pending.get(decision_id)
        if pending is None:
            raise KeyError(f"Decision '{decision_id}' not pending")

        started = time.perf_counter()
        outcome = "applied" if accepted else "rejected"

        with _span(
            "auto_resolve.finalize",
            decision_id=decision_id,
            truth_source=pending.truth_source,
            accepted=accepted,
        ) as span:
            resolved_at = time.time()
            latency_ms = (time.perf_counter() - started) * 1000
            record = ResolutionRecord(
                decision_id=decision_id,
                truth_source=pending.truth_source,
                outcome=outcome,
                resolved_at=resolved_at,
                latency_ms=latency_ms,
                trace_id=pending.trace_id,
                payload={**pending.payload, "finalized_reason": reason}
                if reason
                else pending.payload,
            )
            self._resolved[decision_id] = record
            del self._pending[decision_id]

            duration = time.perf_counter() - started
            _observe_metrics(
                pending.truth_source,
                outcome,
                duration,
                self.backlog_for_source(pending.truth_source),
                self.backlog_total,
                count_decision=True,
            )
            if span is not None:
                span.set_attribute("auto_resolve.outcome", outcome)
                span.set_attribute("auto_resolve.latency_ms", duration * 1000)
                if reason:
                    span.set_attribute("auto_resolve.reason", reason)

        return record

    # ------------------------------------------------------------------
    # Introspection helpers
    # ------------------------------------------------------------------
    @property
    def backlog_total(self) -> int:
        return len(self._pending)

    def backlog_for_source(self, truth_source: str) -> int:
        return sum(
            1 for item in self._pending.values() if item.truth_source == truth_source
        )

    def pending_decisions(self) -> Iterable[PendingDecision]:
        return list(self._pending.values())

    def get_resolution(self, decision_id: str) -> ResolutionRecord:
        record = self._resolved.get(decision_id)
        if record is None:
            raise KeyError(f"Decision '{decision_id}' not resolved")
        return record

    def has_pending(self, decision_id: str) -> bool:
        return decision_id in self._pending

    def clear(self) -> None:
        """Reset internal state. Useful for tests."""

        truth_sources = {item.truth_source for item in self._pending.values()}
        self._pending.clear()
        self._resolved.clear()
        if _BACKLOG_GAUGE is not None:
            for source in truth_sources:
                _BACKLOG_GAUGE.labels(truth_source=source, env=OBS_ENV).set(0)
            _BACKLOG_GAUGE.labels(truth_source="__total__", env=OBS_ENV).set(0)


__all__ = [
    "AutoResolverService",
    "DecisionConflictError",
    "PendingDecision",
    "ResolutionRecord",
]
