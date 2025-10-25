"""Dynamic fee engine with cooldown and anti-thrash controls."""
from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, List, Optional
import math
import time

EPSILON = 1e-9
COOLDOWN_SECONDS = 300
DELTA_LIMIT = 0.20


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
        ts = now if now is not None else time.time()
        raw_depth = max(depth, EPSILON)
        raw_fee = self.base + (self.alpha * volume) + (self.beta * (1.0 / raw_depth))
        clamped_fee = self.bounds.clamp(raw_fee)
        clamped = not math.isclose(clamped_fee, raw_fee, rel_tol=1e-12, abs_tol=1e-12)

        if self._last_update is not None:
            elapsed = ts - self._last_update.ts
            if elapsed < self.cooldown_seconds:
                cooldown_update = FeeUpdate(
                    ts=ts,
                    fee=self._last_update.fee,
                    raw_fee=raw_fee,
                    clamped=clamped,
                    cooldown_applied=True,
                    delta_pct=0.0,
                    reason="cooldown_active",
                )
                self.history.append(cooldown_update)
                return cooldown_update

        fee_candidate = clamped_fee
        delta_pct: Optional[float] = None

        if self._last_update is not None and self._last_update.fee != 0:
            delta_pct = (fee_candidate - self._last_update.fee) / self._last_update.fee
            if abs(delta_pct) > DELTA_LIMIT:
                direction = DELTA_LIMIT if delta_pct > 0 else -DELTA_LIMIT
                fee_candidate = self._last_update.fee * (1 + direction)
                fee_candidate = self.bounds.clamp(fee_candidate)
                delta_pct = direction

        update = FeeUpdate(
            ts=ts,
            fee=fee_candidate,
            raw_fee=raw_fee,
            clamped=clamped_fee != raw_fee,
            cooldown_applied=False,
            delta_pct=delta_pct,
            reason="updated",
        )

        self._last_update = update
        self.history.append(update)
        return update


__all__ = ["FeeEngine", "FeeBounds", "FeeUpdate", "COOLDOWN_SECONDS", "DELTA_LIMIT"]

