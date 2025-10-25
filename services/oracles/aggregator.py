"""Oracle aggregation utilities for quorum-based pricing.

This module implements the Sprint 5 quorum aggregation logic for the
MBP oracles. Quotes are filtered by staleness, aggregated via the
median (quorum price) and scored for divergence.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable, List, Optional
import math
import statistics
import time

STALENESS_THRESHOLD_MS = 30_000
DIVERGENCE_THRESHOLD = 0.01


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
    """Aggregate a collection of quotes using quorum/median logic.

    Parameters
    ----------
    symbol:
        Market symbol for the aggregation.
    quotes:
        Iterable of :class:`Quote` objects.
    now_ms:
        Optional timestamp (epoch milliseconds) used for staleness
        calculations. Defaults to ``time.time()`` when omitted.

    Returns
    -------
    AggregateResult
        Summary of the aggregation outcome.
    """

    resolved_now = now_ms if now_ms is not None else int(time.time() * 1000)
    quotes_list = list(quotes)
    valid: List[Quote] = []
    staleness_values: List[int] = []

    for quote in quotes_list:
        staleness = quote.staleness_ms(resolved_now)
        if staleness <= STALENESS_THRESHOLD_MS and math.isfinite(quote.price):
            valid.append(quote)
            staleness_values.append(staleness)

    total = len(quotes_list)
    if not valid:
        return AggregateResult(
            symbol=symbol,
            agg_price=None,
            quorum_ok=False,
            divergence_pct=None,
            max_staleness_ms=None,
            total_quotes=total,
            valid_sources=[],
            quorum_ratio=0.0,
        )

    prices = sorted(q.price for q in valid)
    median_price = statistics.median(prices)

    if median_price == 0:
        divergence = math.inf
    else:
        divergence = abs(max(prices) - min(prices)) / median_price

    quorum_needed = max(2, math.ceil((2 * total) / 3))
    quorum_ratio = len(valid) / total if total else 0.0
    quorum_ok = len(valid) >= quorum_needed and divergence <= DIVERGENCE_THRESHOLD

    return AggregateResult(
        symbol=symbol,
        agg_price=median_price,
        quorum_ok=quorum_ok,
        divergence_pct=divergence,
        max_staleness_ms=max(staleness_values) if staleness_values else None,
        total_quotes=total,
        valid_sources=[q.source for q in valid],
        quorum_ratio=quorum_ratio,
    )


__all__ = [
    "AggregateResult",
    "Quote",
    "aggregate_quorum",
]

