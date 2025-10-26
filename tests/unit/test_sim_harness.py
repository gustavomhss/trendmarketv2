import json
import os
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in os.sys.path:
    os.sys.path.insert(0, str(ROOT))

from tools.sim_harness import simulate_scenario  # noqa: E402


def test_sim_harness_emits_events(tmp_path: Path):
    fixtures = ROOT / "fixtures"
    events_path = tmp_path / "sim_events.jsonl"
    os.environ["MBP_SIM_EVENT_LOG"] = str(events_path)
    report_path = tmp_path / "report.json"
    result = simulate_scenario(fixtures, "spike", report_path, seed=42)
    assert report_path.exists()
    assert result["scenario"] == "spike"

    contents = [json.loads(line) for line in events_path.read_text(encoding="utf-8").splitlines() if line]
    assert contents
    payload = contents[-1]["payload"]
    assert payload["scenario"] == "spike"
    assert "duration_seconds" in payload
