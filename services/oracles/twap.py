from __future__ import annotations

from collections import deque
from dataclasses import dataclass
from pathlib import Path
from typing import Deque, Dict, List, Optional
import time

from services.telemetry import TelemetryManager, TelemetrySettings

WINDOW_SECONDS = 60
WINDOW_MS = WINDOW_SECONDS * 1000
FAILOVER_THRESHOLD_MS = 60_000

_TELEMETRY = TelemetryManager(TelemetrySettings(service_name="oracle-twap"))
_FETCH_COUNTER = _TELEMETRY.counter(
    "mbp_oracle_fetch_total",
    "Total quote ingestion events handled by the TWAP engine.",
    labelnames=("symbol", "source"),
)
_FETCH_LATENCY = _TELEMETRY.histogram(
    "mbp_oracle_fetch_latency_seconds",
    "Latency between quote timestamp and ingestion time.",
    buckets=(0.001, 0.01, 0.05, 0.1, 0.25, 0.5, 1.0, 2.0),
    labelnames=("symbol", "source"),
)
_TWAP_COMPUTE = _TELEMETRY.histogram(
    "mbp_oracle_twap_compute_seconds",
    "Latency of TWAP window computations.",
    buckets=(0.001, 0.01, 0.05, 0.1, 0.25, 0.5, 1.0),
    labelnames=("symbol",),
)
_TWAP_GAUGE = _TELEMETRY.gauge(
    "mbp_oracle_twap_value",
    "Latest TWAP output per symbol.",
    labelnames=("symbol",),
)
_EVENT_LOG = _TELEMETRY.event_log(
    "MBP_TWAP_EVENT_LOG",
    Path("out/oracles/twap_events.jsonl"),
)


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

    def __init__(
        self, symbol: str, primary: str = "primary", secondary: str = "secondary"
    ) -> None:
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

        now = int(time.time() * 1000)
        lag_seconds = max(0.0, (now - ts_ms) / 1000.0)
        _FETCH_COUNTER.labels(symbol=self.symbol, source=source).inc()
        _FETCH_LATENCY.labels(symbol=self.symbol, source=source).observe(lag_seconds)

        with _TELEMETRY.span(
            "oracle.fetch",
            attributes={
                "oracle.symbol": self.symbol,
                "oracle.source": source,
                "oracle.lag_seconds": lag_seconds,
            },
        ):
            self.sources[source].add(price, ts_ms)
            _EVENT_LOG.emit(
                "oracle.fetch",
                {
                    "symbol": self.symbol,
                    "source": source,
                    "price": price,
                    "ts_ms": ts_ms,
                    "lag_seconds": lag_seconds,
                },
            )

    def compute(self, now_ms: Optional[int] = None) -> Dict[str, object]:
        resolved_now = now_ms if now_ms is not None else int(time.time() * 1000)
        started = time.perf_counter()

        with _TELEMETRY.span(
            "oracle.aggregate",
            attributes={"oracle.symbol": self.symbol, "oracle.window_ms": WINDOW_MS},
        ):
            primary_staleness = self.sources[self.primary].staleness(resolved_now)
            secondary_staleness = self.sources[self.secondary].staleness(resolved_now)

            failover_time_s: Optional[float] = None
            chosen_source = self.primary

            if primary_staleness is None or primary_staleness > FAILOVER_THRESHOLD_MS:
                if (
                    secondary_staleness is not None
                    and secondary_staleness <= FAILOVER_THRESHOLD_MS
                ):
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

        duration = time.perf_counter() - started
        if twap_value is not None:
            _TWAP_GAUGE.labels(symbol=self.symbol).set(twap_value)
        _TWAP_COMPUTE.labels(symbol=self.symbol).observe(duration)
        _EVENT_LOG.emit(
            "oracle.twap",
            {
                "symbol": self.symbol,
                "source": chosen_source,
                "twap": twap_value,
                "staleness_ms": window.staleness(resolved_now),
                "failover_time_s": failover_time_s,
                "duration_seconds": duration,
            },
        )

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


__all__ = [
    "TwapEngine",
    "TwapEvent",
    "PriceWindow",
    "WINDOW_SECONDS",
    "FAILOVER_THRESHOLD_MS",
]
