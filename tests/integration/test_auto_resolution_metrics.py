import sys
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from services.auto_resolution.service import AutoResolutionService  # noqa: E402


def test_metrics_and_events_written(tmp_path: Path) -> None:
    service = AutoResolutionService(
        audit_log=tmp_path / "audit.jsonl",
        event_log=tmp_path / "events.jsonl",
        metrics_log=tmp_path / "metrics.jsonl",
    )

    service.apply(
        event_id="evt-m-1",
        symbol="ETHUSD",
        truth={"value": 2300.0, "source": "truth_feed", "ts": 1700001234},
        quorum={
            "value": 2300.5,
            "quorum_ok": True,
            "diverg_pct": 0.0002,
            "staleness_ms": 1200,
        },
        actor="auto_resolver",
        role="system",
    )

    metrics_path = tmp_path / "metrics.jsonl"
    events_path = tmp_path / "events.jsonl"

    metrics = [json.loads(line) for line in metrics_path.read_text().splitlines()]
    events = [json.loads(line) for line in events_path.read_text().splitlines()]

    assert metrics[0]["event_id"] == "evt-m-1"
    assert events[0]["decision_id"]
    assert events[0]["schema_version"] == 1
