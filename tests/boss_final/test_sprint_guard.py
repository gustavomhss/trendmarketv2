from __future__ import annotations

import json
from pathlib import Path

import pytest

from scripts.boss_final import sprint_guard


def _freeze_time(monkeypatch: pytest.MonkeyPatch, timestamp: str = "2024-01-02T11:00:00Z") -> None:
    monkeypatch.setattr(sprint_guard, "isoformat_utc", lambda: timestamp)


def test_run_stage_writes_outputs(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    output_root = tmp_path / "stages"
    monkeypatch.setattr(sprint_guard, "OUTPUT_ROOT", output_root)
    _freeze_time(monkeypatch, "2024-01-02T12:00:00Z")

    def handler(context: sprint_guard.StageContext) -> None:
        sprint_guard.record_check(
            context,
            name="synthetic",
            code="S1-SYNTH",
            passed=True,
            detail="ok",
        )

    monkeypatch.setitem(sprint_guard.STAGE_HANDLERS, "s1", handler)

    sprint_guard.run_stage("s1", "primary")
    sprint_guard.run_stage("s1", "clean")

    primary_dir = output_root / "s1" / "primary"
    assert (primary_dir / "result.json").exists()
    stage_summary = json.loads((output_root / "s1" / "summary.json").read_text(encoding="utf-8"))
    assert stage_summary["status"] == "PASS"
    assert stage_summary["variants"]["primary"]["status"] == "PASS"
    assert stage_summary["variants"]["clean"]["status"] == "PASS"
    stage_guard = (output_root / "s1" / "guard_status.txt").read_text(encoding="utf-8").strip()
    assert stage_guard == "PASS"


def test_run_stage_failure_sets_fail(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    output_root = tmp_path / "stages"
    monkeypatch.setattr(sprint_guard, "OUTPUT_ROOT", output_root)
    _freeze_time(monkeypatch)

    def handler(_: sprint_guard.StageContext) -> None:
        raise sprint_guard.StageFailure("S1-TEST", "falha simulada")

    monkeypatch.setitem(sprint_guard.STAGE_HANDLERS, "s1", handler)

    with pytest.raises(SystemExit):
        sprint_guard.run_stage("s1", "primary")

    primary_guard = (output_root / "s1" / "primary" / "guard_status.txt").read_text(encoding="utf-8").strip()
    assert primary_guard == "FAIL"
    summary = json.loads((output_root / "s1" / "summary.json").read_text(encoding="utf-8"))
    assert summary["status"] == "FAIL"


def test_validate_dashboard_structure_pass(monkeypatch: pytest.MonkeyPatch) -> None:
    context = sprint_guard.StageContext(stage="s5", variant="primary")
    sprint_guard.validate_dashboard_structure(context)
    record = context.records[-1]
    assert record.name == "Grafana dashboard"
    assert record.status == "PASS"


def test_validate_dashboard_structure_fail(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    dashboards_dir = tmp_path / "dashboards" / "grafana"
    dashboards_dir.mkdir(parents=True)
    bad_dashboard = dashboards_dir / "scorecards_quorum_failover_staleness.json"
    bad_dashboard.write_text(json.dumps({"title": "broken", "panels": []}), encoding="utf-8")

    monkeypatch.setattr(sprint_guard, "BASE_DIR", tmp_path)
    context = sprint_guard.StageContext(stage="s5", variant="primary")

    with pytest.raises(sprint_guard.StageFailure):
        sprint_guard.validate_dashboard_structure(context)


def test_validate_actions_lock_json(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    base = tmp_path
    actions_lock = {
        "actions/checkout": {
            "sha": "b4ffde65f46336ab3f3460e4f9d6a7152fb7a3b6",
            "date": "2024-09-15",
            "author": "GitHub Actions",
            "rationale": "Checkout",
        }
    }
    (base / "actions.lock").write_text(json.dumps(actions_lock, indent=2) + "\n", encoding="utf-8")
    workflows_dir = base / ".github" / "workflows"
    workflows_dir.mkdir(parents=True, exist_ok=True)
    workflow = workflows_dir / "test.yml"
    workflow.write_text(
        "\n".join(
            [
                "name: test",
                "on: [push]",
                "jobs:",
                "  build:",
                "    runs-on: ubuntu-latest",
                "    steps:",
                "      - uses: actions/checkout@b4ffde65f46336ab3f3460e4f9d6a7152fb7a3b6",
            ]
        ),
        encoding="utf-8",
    )

    monkeypatch.setattr(sprint_guard, "BASE_DIR", base)
    context = sprint_guard.StageContext(stage="s4", variant="primary")
    sprint_guard.validate_actions_lock(context)

    assert context.records[-2].status == "PASS"
    assert context.records[-1].status == "PASS"
