from __future__ import annotations

import json
from datetime import datetime, timezone
from decimal import Decimal
from pathlib import Path

import pytest

from scripts.boss_final import aggregate_q1


def _freeze_datetime(monkeypatch: pytest.MonkeyPatch) -> None:
    class FrozenDateTime(datetime):
        @classmethod
        def now(cls, tz: timezone | None = None) -> datetime:
            return datetime(2024, 1, 1, 9, 30, 0, tzinfo=tz or timezone.utc)

    monkeypatch.setattr(aggregate_q1, "datetime", FrozenDateTime)


def _write_stage(
    stages_dir: Path,
    stage: str,
    status: str,
    score: Decimal,
    on_fail: str = "Investigate",
) -> None:
    payload = {
        "schema_version": 1,
        "stage": stage,
        "status": status,
        "score": f"{score}",
        "formatted_score": f"{score.quantize(Decimal('0.0001'))}",
        "generated_at": "2024-01-01T00:00:00Z",
        "on_fail": on_fail,
    }
    (stages_dir / f"{stage}.json").write_text(json.dumps(payload), encoding="utf-8")


def _write_guard(stages_dir: Path, stage: str, status: str) -> None:
    (stages_dir / f"{stage}{aggregate_q1.STAGE_GUARD_SUFFIX}").write_text(status + "\n", encoding="utf-8")


def _prepare_environment(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> tuple[Path, Path]:
    stages_dir = tmp_path / "stages"
    output_dir = tmp_path / "boss"
    stages_dir.mkdir()
    output_dir.mkdir()
    monkeypatch.setattr(aggregate_q1, "STAGES_DIR", stages_dir)
    monkeypatch.setattr(aggregate_q1, "OUTPUT_DIR", output_dir)
    _freeze_datetime(monkeypatch)
    return stages_dir, output_dir


def test_aggregate_pass_flow_generates_artifacts(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    stages_dir, output_dir = _prepare_environment(tmp_path, monkeypatch)
    scores: list[Decimal] = []
    for index, stage in enumerate(aggregate_q1.STAGES):
        score = Decimal("0.9700") + Decimal(index) * Decimal("0.0010")
        scores.append(score)
        _write_stage(stages_dir, stage, "pass", score)
        _write_guard(stages_dir, stage, "PASS")

    assert aggregate_q1.main() == 0

    report = json.loads((output_dir / "report.json").read_text(encoding="utf-8"))
    assert report["summary"]["status"] == "pass"
    expected_ratio = sum(scores) / Decimal(len(scores))
    expected_ratio = expected_ratio.quantize(Decimal("0.0001"))
    assert report["summary"]["aggregate_ratio"] == str(expected_ratio)
    dag_svg = (output_dir / "dag.svg").read_text(encoding="utf-8")
    for stage in aggregate_q1.STAGES:
        assert stage.upper() in dag_svg
    badge_svg = (output_dir / "badge.svg").read_text(encoding="utf-8")
    assert "Q1 PASS" in badge_svg
    guard_status = (output_dir / "guard_status.txt").read_text(encoding="utf-8").strip()
    assert guard_status == "PASS"


def test_aggregate_guard_failure_propagates(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    stages_dir, output_dir = _prepare_environment(tmp_path, monkeypatch)
    failing_stage = "s4"
    for stage in aggregate_q1.STAGES:
        _write_stage(stages_dir, stage, "pass", Decimal("0.9800"))
        status = "FAIL" if stage == failing_stage else "PASS"
        _write_guard(stages_dir, stage, status)

    assert aggregate_q1.main() == 0

    report = json.loads((output_dir / "report.json").read_text(encoding="utf-8"))
    assert report["summary"]["status"] == "fail"
    assert any(entry["stage"] == failing_stage and entry["status"] == "fail" for entry in report["stages"])
    guard_status = (output_dir / "guard_status.txt").read_text(encoding="utf-8").strip()
    assert guard_status == "FAIL"


def test_missing_guard_status_fails_fast(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    stages_dir, output_dir = _prepare_environment(tmp_path, monkeypatch)
    for stage in aggregate_q1.STAGES:
        _write_stage(stages_dir, stage, "pass", Decimal("0.9800"))
        if stage != "s2":
            _write_guard(stages_dir, stage, "PASS")

    with pytest.raises(SystemExit) as exc:
        aggregate_q1.main()
    assert exc.value.code == 1
    assert (output_dir / "guard_status.txt").read_text(encoding="utf-8").strip() == "FAIL"


def test_guard_status_divergence_is_reported(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    stages_dir, output_dir = _prepare_environment(tmp_path, monkeypatch)
    for stage in aggregate_q1.STAGES:
        status = "fail" if stage == "s1" else "pass"
        _write_stage(stages_dir, stage, status, Decimal("0.9800"))
        guard = "PASS" if stage == "s1" else "PASS"
        _write_guard(stages_dir, stage, guard)

    with pytest.raises(SystemExit) as exc:
        aggregate_q1.main()
    assert exc.value.code == 1
    assert (output_dir / "guard_status.txt").read_text(encoding="utf-8").strip() == "FAIL"
