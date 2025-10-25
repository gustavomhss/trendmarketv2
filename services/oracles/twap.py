"""Time weighted average price (TWAP) engine with failover semantics."""
from __future__ import annotations

from collections import deque
from dataclasses import dataclass
from typing import Deque, Dict, List, Optional
import time

WINDOW_SECONDS = 60
WINDOW_MS = WINDOW_SECONDS * 1000
FAILOVER_THRESHOLD_MS = 60_000


@dataclass
class TwapEvent:
    """Structured event emitted by the TWAP engine."""

    ts_ms: int
    kind: str
    details: Dict[str, object]


class PriceWindow:
    """Maintains a rolling price window for TWAP calculations."""

    def __init__(self, window_ms: int = WINDOW_MS) -> None:
        self.window_ms = window_ms
        self.samples: Deque[tuple[int, float]] = deque()

    def add(self, price: float, ts_ms: int) -> None:
        if self.samples and ts_ms < self.samples[-1][0]:
            raise ValueError("Quotes must arrive in non-decreasing order")
        self.samples.append((ts_ms, price))
        self._trim(ts_ms)

    def _trim(self, now_ms: int) -> None:
        window_start = now_ms - self.window_ms
        while len(self.samples) > 1 and self.samples[1][0] <= window_start:
            self.samples.popleft()

    def staleness(self, now_ms: int) -> Optional[int]:
        if not self.samples:
            return None
        return max(0, now_ms - self.samples[-1][0])

    def compute(self, now_ms: int) -> Optional[float]:
        if not self.samples:
            return None

        window_start = now_ms - self.window_ms
        segments: List[tuple[int, float]] = []

        price_at_start = self._price_at(window_start)
        segments.append((window_start, price_at_start))

        for ts_ms, price in self.samples:
            if ts_ms >= window_start:
                segments.append((ts_ms, price))

        if segments[-1][0] != now_ms:
            segments.append((now_ms, segments[-1][1]))

        total = 0.0
        for (t0, price0), (t1, _) in zip(segments, segments[1:]):
            if t1 <= t0:
                continue
            total += price0 * (t1 - t0)

        return total / self.window_ms if self.window_ms else None

    def _price_at(self, ts_ms: int) -> float:
        if not self.samples:
            return 0.0
        for sample_ts, price in reversed(self.samples):
            if sample_ts <= ts_ms:
                return price
        return self.samples[0][1]


class TwapEngine:
    """TWAP engine with automatic failover between price sources."""

    def __init__(self, symbol: str, primary: str = "primary", secondary: str = "secondary") -> None:
        self.symbol = symbol
        self.sources = {
            primary: PriceWindow(),
            secondary: PriceWindow(),
        }
        self.primary = primary
        self.secondary = secondary
        self.active_source = primary
        self.events: List[TwapEvent] = []

    def ingest(self, source: str, price: float, ts_ms: int) -> None:
        if source not in self.sources:
            raise KeyError(f"Unknown source '{source}'")
        self.sources[source].add(price, ts_ms)

    def compute(self, now_ms: Optional[int] = None) -> Dict[str, object]:
        resolved_now = now_ms if now_ms is not None else int(time.time() * 1000)
        primary_staleness = self.sources[self.primary].staleness(resolved_now)
        secondary_staleness = self.sources[self.secondary].staleness(resolved_now)

        failover_time_s: Optional[float] = None
        chosen_source = self.primary

        if primary_staleness is None or primary_staleness > FAILOVER_THRESHOLD_MS:
            if secondary_staleness is not None and secondary_staleness <= FAILOVER_THRESHOLD_MS:
                chosen_source = self.secondary
                failover_time_s = round(secondary_staleness / 1000.0, 6)
                if self.active_source != self.secondary:
                    self.events.append(
                        TwapEvent(
                            ts_ms=resolved_now,
                            kind="failover",
                            details={
                                "from": self.primary,
                                "to": self.secondary,
                                "failover_time_s": failover_time_s,
                            },
                        )
                    )
                self.active_source = self.secondary
            else:
                self.active_source = self.primary
        else:
            self.active_source = self.primary

        window = self.sources[chosen_source]
        twap_value = window.compute(resolved_now)

        return {
            "symbol": self.symbol,
            "source": chosen_source,
            "twap": twap_value,
            "staleness_ms": window.staleness(resolved_now),
            "failover_time_s": failover_time_s,
            "quorum_source": self.active_source,
        }

    def snapshot_events(self) -> List[TwapEvent]:
        return list(self.events)


__all__ = ["TwapEngine", "TwapEvent", "PriceWindow", "WINDOW_SECONDS", "FAILOVER_THRESHOLD_MS"]



