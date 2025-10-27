import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from services.oracles.aggregator import Quote, aggregate_quorum  # noqa: E402


def test_quorum_succeeds_with_valid_quotes():
    now_ms = 1_700_000_000_000
    quotes = [
        Quote(symbol="BRLUSD", price=5.43, ts_ms=now_ms - 5_000, source="alpha"),
        Quote(symbol="BRLUSD", price=5.44, ts_ms=now_ms - 10_000, source="beta"),
        Quote(symbol="BRLUSD", price=5.42, ts_ms=now_ms - 15_000, source="gamma"),
    ]

    result = aggregate_quorum("BRLUSD", quotes, now_ms=now_ms)
    assert result.quorum_ok is True
    assert abs(result.agg_price - 5.43) < 1e-9
    assert result.divergence_pct is not None and result.divergence_pct <= 0.01
    assert result.quorum_ratio >= (2 / 3)
    assert result.staleness_ok is True


def test_quorum_fails_on_high_divergence():
    now_ms = 1_700_000_000_000
    quotes = [
        Quote(symbol="BRLUSD", price=5.30, ts_ms=now_ms - 5_000, source="alpha"),
        Quote(symbol="BRLUSD", price=5.70, ts_ms=now_ms - 5_000, source="beta"),
    ]

    result = aggregate_quorum("BRLUSD", quotes, now_ms=now_ms)
    assert result.quorum_ok is False
    assert result.divergence_pct is not None and result.divergence_pct > 0.01
