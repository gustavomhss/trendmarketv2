import importlib
import json
import os
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in os.sys.path:
    os.sys.path.insert(0, str(ROOT))


@pytest.fixture
def oracle_module(tmp_path: Path):
    events = tmp_path / "events.jsonl"
    os.environ["MBP_ORACLE_EVENT_LOG"] = str(events)
    module = importlib.import_module("services.oracles.aggregator")
    importlib.reload(module)
    yield module
    if "services.oracles.aggregator" in os.sys.modules:
        del os.sys.modules["services.oracles.aggregator"]


def test_oracle_event_emission(oracle_module, tmp_path: Path):
    quote_cls = oracle_module.Quote
    quotes = [
        quote_cls(
            symbol="BRLUSD",
            price=100.0 + idx * 0.1,
            ts_ms=1_000_000 + idx * 100,
            source=f"src{idx}",
        )
        for idx in range(3)
    ]
    result = oracle_module.aggregate_quorum("BRLUSD", quotes, now_ms=1_000_500)
    assert result.quorum_ok

    events_path = Path(os.environ["MBP_ORACLE_EVENT_LOG"])
    assert events_path.exists()
    contents = [
        json.loads(line)
        for line in events_path.read_text(encoding="utf-8").splitlines()
        if line
    ]
    assert contents
    payload = contents[-1]["payload"]
    assert payload["symbol"] == "BRLUSD"
    assert payload["quorum_ok"] is True
    assert payload["quorum_ratio"] >= 2 / 3
    assert payload["valid_sources"] == ["src0", "src1", "src2"]
    assert payload["divergence_pct"] is not None
    assert payload["duration_seconds"] >= 0
