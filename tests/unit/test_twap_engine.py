import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from services.oracles.twap import FAILOVER_THRESHOLD_MS, TwapEngine  # noqa: E402


def test_twap_failover_to_secondary_when_primary_stale():
    engine = TwapEngine(symbol="BRLUSD")
    base = 1_700_000_000_000

    engine.ingest("primary", 5.40, base)
    engine.ingest("secondary", 5.41, base)
    engine.ingest("primary", 5.41, base + 30_000)
    engine.ingest("secondary", 5.42, base + 30_000)

    engine.ingest("secondary", 5.43, base + 100_000)

    snapshot = engine.compute(now_ms=base + 120_000)
    assert snapshot["source"] == "secondary"
    assert snapshot["failover_time_s"] is not None
    assert snapshot["failover_time_s"] <= FAILOVER_THRESHOLD_MS / 1000
    events = engine.snapshot_events()
    assert any(evt.kind == "failover" for evt in events)

