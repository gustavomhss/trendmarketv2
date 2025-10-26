from __future__ import annotations

import json
from pathlib import Path

import pytest

from scripts.boss_final import aggregate_q1, sprint_guard


def test_run_stage_writes_outputs(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    stage_dir = tmp_path / "stages"
    monkeypatch.setattr(sprint_guard, "OUTPUT_ROOT", stage_dir)

    def handler(context: sprint_guard.StageContext) -> None:
        context.records.append(
            sprint_guard.CommandRecord(
                name="dummy",
                command=None,
                status="PASS",
                returncode=0,
                duration_seconds=0.0,
                stdout="ok",
                stderr="",
            )
        )

    monkeypatch.setitem(sprint_guard.STAGE_HANDLERS, "s1", handler)
    result = sprint_guard.run_stage("s1", "primary")

    assert result["status"] == "PASS"
    guard_status = (stage_dir / "s1" / "primary" / "guard_status.txt").read_text(encoding="utf-8").strip()
    assert guard_status == "PASS"


def test_run_stage_failure_sets_fail(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    stage_dir = tmp_path / "stages"
    monkeypatch.setattr(sprint_guard, "OUTPUT_ROOT", stage_dir)

    def handler(_: sprint_guard.StageContext) -> None:
        raise sprint_guard.StageFailure("S1-TEST", "falha simulada")

    monkeypatch.setitem(sprint_guard.STAGE_HANDLERS, "s1", handler)

    with pytest.raises(SystemExit):
        sprint_guard.run_stage("s1", "primary")

    guard_status = (stage_dir / "s1" / "primary" / "guard_status.txt").read_text(encoding="utf-8").strip()
    assert guard_status == "FAIL"


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


def _write_stage(tmp_path: Path, stage: str, variant: str, status: str, notes: str) -> None:
    result_dir = tmp_path / "stages" / stage / variant
    result_dir.mkdir(parents=True, exist_ok=True)
    payload = {
        "stage": stage,
        "variant": variant,
        "status": status,
        "notes": notes,
        "timestamp_utc": "2024-01-01T00:00:00Z",
    }
    (result_dir / "result.json").write_text(json.dumps(payload), encoding="utf-8")
    (result_dir / "guard_status.txt").write_text(f"{status}\n", encoding="utf-8")


def test_aggregate_pass(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    for stage in sprint_guard.STAGES:
        _write_stage(tmp_path, stage, "primary", "PASS", "primary ok")
        _write_stage(tmp_path, stage, "clean", "PASS", "clean ok")

    monkeypatch.setattr(aggregate_q1, "OUTPUT_DIR", tmp_path)
    monkeypatch.setattr(aggregate_q1, "STAGES_DIR", tmp_path / "stages")

    artifacts = aggregate_q1.aggregate("v1.0.0")
    assert artifacts.report["status"] == "PASS"
    report = json.loads((tmp_path / "report.json").read_text(encoding="utf-8"))
    assert report["release_tag"] == "v1.0.0"
    assert (tmp_path / "bundle.sha256").read_text(encoding="utf-8").strip() == artifacts.bundle_sha256


def test_aggregate_fail_on_stage_failure(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    for stage in sprint_guard.STAGES:
        _write_stage(tmp_path, stage, "primary", "PASS", "primary ok")
        _write_stage(tmp_path, stage, "clean", "PASS", "clean ok")
    _write_stage(tmp_path, "s3", "clean", "FAIL", "clean failed")

    monkeypatch.setattr(aggregate_q1, "OUTPUT_DIR", tmp_path)
    monkeypatch.setattr(aggregate_q1, "STAGES_DIR", tmp_path / "stages")

    with pytest.raises(SystemExit):
        aggregate_q1.aggregate(None)

    guard_status = (tmp_path / "guard_status.txt").read_text(encoding="utf-8").strip()
    assert guard_status == "FAIL"
