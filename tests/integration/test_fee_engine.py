import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from services.fees.engine import COOLDOWN_SECONDS, DELTA_LIMIT, FeeBounds, FeeEngine  # noqa: E402


def test_fee_engine_enforces_bounds_and_cooldown():
    bounds = FeeBounds(minimum=0.0005, maximum=0.0050)
    engine = FeeEngine(base=0.0010, alpha=0.00002, beta=0.0005, bounds=bounds)

    first = engine.update_fee(volume=1000, depth=5000, now=0)
    assert bounds.minimum <= first.fee <= bounds.maximum
    assert first.cooldown_applied is False
    assert first.delta_pct is None

    cooldown = engine.update_fee(volume=5000, depth=1000, now=COOLDOWN_SECONDS - 1)
    assert cooldown.fee == first.fee
    assert cooldown.cooldown_applied is True

    third = engine.update_fee(volume=5000, depth=800, now=COOLDOWN_SECONDS + 1)
    assert third.cooldown_applied is False
    assert third.delta_pct is not None
    assert abs(third.delta_pct) <= DELTA_LIMIT
    assert third.fee <= bounds.maximum
    assert len(engine.history) == 3

