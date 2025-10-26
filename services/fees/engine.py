from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import List, Optional
import math
import time

from services.telemetry import TelemetryManager, TelemetrySettings

EPSILON = 1e-9
COOLDOWN_SECONDS = 300
DELTA_LIMIT = 0.20

_TELEMETRY = TelemetryManager(TelemetrySettings(service_name="fee-engine"))
_FEE_LATENCY = _TELEMETRY.histogram(
    "mbp_fee_update_duration_seconds",
    "Latency of fee update computations.",
    buckets=(0.001, 0.01, 0.05, 0.1, 0.25, 0.5, 1.0),
)
_FEE_COUNTER = _TELEMETRY.counter(
    "mbp_fee_update_total",
    "Total fee updates split by outcome.",
    labelnames=("reason",),
)
_FEE_DELTA = _TELEMETRY.gauge(
    "mbp_fee_delta_pct",
    "Last fee delta percentage applied by the engine.",
)
_EVENT_LOG = _TELEMETRY.event_log(
    "MBP_FEE_EVENT_LOG",
    Path("out/fees/events.jsonl"),
)


@dataclass(frozen=True)
class FeeBounds:
    minimum: float
    maximum: float

    def clamp(self, value: float) -> float:
        return max(self.minimum, min(self.maximum, value))


@dataclass
class FeeUpdate:
    ts: float
    fee: float
    raw_fee: float
    clamped: bool
    cooldown_applied: bool
    delta_pct: Optional[float]
    reason: str


class FeeEngine:
    """Compute dynamic fees constrained by cooldown and delta bounds."""

    def __init__(
        self,
        *,
        base: float,
        alpha: float,
        beta: float,
        bounds: FeeBounds,
        cooldown_seconds: int = COOLDOWN_SECONDS,
    ) -> None:
        self.base = base
        self.alpha = alpha
        self.beta = beta
        self.bounds = bounds
        self.cooldown_seconds = cooldown_seconds
        self._last_update: Optional[FeeUpdate] = None
        self.history: List[FeeUpdate] = []

    def update_fee(
        self,
        *,
        volume: float,
        depth: float,
        now: Optional[float] = None,
    ) -> FeeUpdate:
        started = time.perf_counter()
        ts = now if now is not None else time.time()
        raw_depth = max(depth, EPSILON)
        raw_fee = self.base + (self.alpha * volume) + (self.beta * (1.0 / raw_depth))
        clamped_fee = self.bounds.clamp(raw_fee)
        clamped = not math.isclose(clamped_fee, raw_fee, rel_tol=1e-12, abs_tol=1e-12)

        reason = "updated"
        cooldown_applied = False

        if self._last_update is not None:
            elapsed = ts - self._last_update.ts
            if elapsed < self.cooldown_seconds:
                cooldown_applied = True
                reason = "cooldown_active"
                update = FeeUpdate(
                    ts=ts,
                    fee=self._last_update.fee,
                    raw_fee=raw_fee,
                    clamped=clamped,
                    cooldown_applied=True,
                    delta_pct=0.0,
                    reason=reason,
                )
                self.history.append(update)
                self._record_metrics(update, started)
                return update

        fee_candidate = clamped_fee
        delta_pct: Optional[float] = None

        if self._last_update is not None and self._last_update.fee != 0:
            delta_pct = (fee_candidate - self._last_update.fee) / self._last_update.fee
            if abs(delta_pct) > DELTA_LIMIT:
                direction = DELTA_LIMIT if delta_pct > 0 else -DELTA_LIMIT
                fee_candidate = self._last_update.fee * (1 + direction)
                fee_candidate = self.bounds.clamp(fee_candidate)
                delta_pct = direction
                reason = "delta_clamped"

        update = FeeUpdate(
            ts=ts,
            fee=fee_candidate,
            raw_fee=raw_fee,
            clamped=clamped_fee != raw_fee,
            cooldown_applied=cooldown_applied,
            delta_pct=delta_pct,
            reason=reason,
        )

        self._last_update = update
        self.history.append(update)
        self._record_metrics(update, started)
        return update

    # ------------------------------------------------------------------
    def _record_metrics(self, update: FeeUpdate, started: float) -> None:
        duration = time.perf_counter() - started
        _FEE_LATENCY.observe(duration)
        _FEE_COUNTER.labels(reason=update.reason).inc()
        if update.delta_pct is not None:
            _FEE_DELTA.set(update.delta_pct)
        _EVENT_LOG.emit(
            "fee.update",
            {
                "ts": update.ts,
                "fee": update.fee,
                "raw_fee": update.raw_fee,
                "delta_pct": update.delta_pct,
                "clamped": update.clamped,
                "cooldown_applied": update.cooldown_applied,
                "reason": update.reason,
                "duration_seconds": duration,
            },
        )


__all__ = ["FeeEngine", "FeeBounds", "FeeUpdate", "COOLDOWN_SECONDS", "DELTA_LIMIT"]
