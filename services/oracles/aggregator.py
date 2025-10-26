"""Oracle aggregation utilities for quorum-based pricing.

This module implements the Sprint 5 quorum aggregation logic for the
MBP oracles. Quotes are filtered by staleness, aggregated via the
median (quorum price) and scored for divergence.
"""
from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, List, Optional
import math
import statistics
import time

from services.telemetry import TelemetryManager, TelemetrySettings

STALENESS_THRESHOLD_MS = 30_000
DIVERGENCE_THRESHOLD = 0.01

_TELEMETRY = TelemetryManager(TelemetrySettings(service_name="oracle-aggregator"))
_AGG_LATENCY = _TELEMETRY.histogram(
    "mbp_oracle_aggregate_duration_seconds",
    "Latency of oracle aggregation operations.",
    buckets=(
        0.001,
        0.005,
        0.01,
        0.025,
        0.05,
        0.1,
        0.25,
        0.5,
        1.0,
    ),
    labelnames=("symbol",),
)
_AGG_COUNTER = _TELEMETRY.counter(
    "mbp_oracle_aggregate_total",
    "Total oracle aggregation evaluations grouped by quorum result.",
    labelnames=("symbol", "quorum_ok"),
)
_AGG_DIVERGENCE = _TELEMETRY.gauge(
    "mbp_oracle_divergence_pct",
    "Latest divergence ratio produced by the oracle aggregator.",
    labelnames=("symbol",),
)
_EVENT_LOG = _TELEMETRY.event_log(
    "MBP_ORACLE_EVENT_LOG",
    Path("out/oracles/quorum_events.jsonl"),
)


@dataclass(frozen=True)
class Quote:
    """Representation of a price quote emitted by an oracle source."""

    symbol: str
    price: float
    ts_ms: int
    source: str

    def staleness_ms(self, now_ms: Optional[int] = None) -> int:
        """Return the staleness of the quote in milliseconds."""

        now = now_ms if now_ms is not None else int(time.time() * 1000)
        return max(0, now - self.ts_ms)


@dataclass
class AggregateResult:
    """Result emitted by :func:`aggregate_quorum`."""

    symbol: str
    agg_price: Optional[float]
    quorum_ok: bool
    divergence_pct: Optional[float]
    max_staleness_ms: Optional[int]
    total_quotes: int
    valid_sources: List[str]
    quorum_ratio: float

    @property
    def staleness_ok(self) -> bool:
        """Return ``True`` when the aggregated quotes are fresh enough."""

        if self.max_staleness_ms is None:
            return False
        return self.max_staleness_ms <= STALENESS_THRESHOLD_MS


def aggregate_quorum(
    symbol: str,
    quotes: Iterable[Quote],
    *,
    now_ms: Optional[int] = None,
) -> AggregateResult:
    """Aggregate a collection of quotes using quorum/median logic."""

    resolved_now = now_ms if now_ms is not None else int(time.time() * 1000)
    started = time.perf_counter()

    quotes_list = list(quotes)
    span_attributes = {"oracle.symbol": symbol, "oracle.total_quotes": len(quotes_list)}

    with _TELEMETRY.span("oracle.aggregate", attributes=span_attributes):
        valid: List[Quote] = []
        staleness_values: List[int] = []

        for quote in quotes_list:
            staleness = quote.staleness_ms(resolved_now)
            if staleness <= STALENESS_THRESHOLD_MS and math.isfinite(quote.price):
                valid.append(quote)
                staleness_values.append(staleness)

        total = len(quotes_list)
        if not valid:
            result = AggregateResult(
                symbol=symbol,
                agg_price=None,
                quorum_ok=False,
                divergence_pct=None,
                max_staleness_ms=None,
                total_quotes=total,
                valid_sources=[],
                quorum_ratio=0.0,
            )
        else:
            prices = sorted(q.price for q in valid)
            median_price = statistics.median(prices)

            if median_price == 0:
                divergence = math.inf
            else:
                divergence = abs(max(prices) - min(prices)) / median_price

            quorum_needed = max(2, math.ceil((2 * total) / 3))
            quorum_ratio = len(valid) / total if total else 0.0
            quorum_ok = len(valid) >= quorum_needed and divergence <= DIVERGENCE_THRESHOLD

            result = AggregateResult(
                symbol=symbol,
                agg_price=median_price,
                quorum_ok=quorum_ok,
                divergence_pct=divergence,
                max_staleness_ms=max(staleness_values) if staleness_values else None,
                total_quotes=total,
                valid_sources=[q.source for q in valid],
                quorum_ratio=quorum_ratio,
            )

    duration = time.perf_counter() - started
    _AGG_LATENCY.labels(symbol=symbol).observe(duration)
    _AGG_COUNTER.labels(symbol=symbol, quorum_ok=str(result.quorum_ok).lower()).inc()
    if result.divergence_pct is not None and math.isfinite(result.divergence_pct):
        _AGG_DIVERGENCE.labels(symbol=symbol).set(result.divergence_pct)
    _EVENT_LOG.emit(
        "oracle.aggregate",
        {
            "symbol": symbol,
            "quorum_ok": result.quorum_ok,
            "quorum_ratio": result.quorum_ratio,
            "valid_sources": result.valid_sources,
            "divergence_pct": result.divergence_pct,
            "agg_price": result.agg_price,
            "max_staleness_ms": result.max_staleness_ms,
            "total_quotes": result.total_quotes,
            "duration_seconds": duration,
        },
    )
    return result


__all__ = [
    "AggregateResult",
    "Quote",
    "aggregate_quorum",
]
