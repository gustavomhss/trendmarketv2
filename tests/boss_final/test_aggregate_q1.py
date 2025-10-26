from __future__ import annotations

import json
from decimal import Decimal
from pathlib import Path

import pytest

from scripts.boss_final import aggregate_q1


def _freeze_time(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(aggregate_q1, "isoformat_utc", lambda: "2024-01-01T09:30:00Z")


def _prepare_environment(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> tuple[Path, Path]:
    stages_dir = tmp_path / "stages"
    output_dir = tmp_path / "boss"
    stages_dir.mkdir()
    output_dir.mkdir()
    monkeypatch.setattr(aggregate_q1, "STAGES_DIR", stages_dir)
    monkeypatch.setattr(aggregate_q1, "OUTPUT_DIR", output_dir)
    _freeze_time(monkeypatch)
    return stages_dir, output_dir


def _write_stage(
    stages_dir: Path,
    stage: str,
    *,
    status: str,
    score: Decimal,
    guard: str,
    notes: str | None = None,
    on_fail: str | None = None,
) -> None:
    payload: dict[str, object] = {
        "schema_version": 1,
        "stage": stage,
        "status": status,
        "score": f"{score}",
        "formatted_score": f"{score.quantize(Decimal('0.0001'))}",
        "generated_at": "2024-01-01T00:00:00Z",
    }
    if notes is not None:
        payload["notes"] = notes
    if on_fail is not None:
        payload["on_fail"] = on_fail
    (stages_dir / f"{stage}.json").write_text(json.dumps(payload), encoding="utf-8")
    (stages_dir / f"{stage}{aggregate_q1.STAGE_GUARD_SUFFIX}").write_text(guard + "
", encoding="utf-8")


def test_generate_report_success(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    stages_dir, output_dir = _prepare_environment(tmp_path, monkeypatch)
    scores: list[Decimal] = []
    for idx, stage in enumerate(aggregate_q1.STAGES):
        score = Decimal("0.9700") + Decimal(idx) * Decimal("0.0010")
        scores.append(score)
        _write_stage(stages_dir, stage, status="PASS", score=score, guard="PASS", notes="All good")

    artifacts = aggregate_q1.generate_report()

    assert artifacts.summary["status"] == "PASS"
    expected_ratio = (sum(scores) / Decimal(len(scores))).quantize(Decimal("0.0001"))
    assert Decimal(artifacts.summary["aggregate_ratio"]) == expected_ratio
    report = json.loads((output_dir / "report.json").read_text(encoding="utf-8"))
    assert report["status"] == "PASS"
    assert report["sprints"]["s1"]["notes"] == "All good"
    badge = (output_dir / "badge.svg").read_text(encoding="utf-8")
    assert "Q1 PASS" in badge
    guard_status = (output_dir / "guard_status.txt").read_text(encoding="utf-8").strip()
    assert guard_status == "PASS"


def test_guard_failure_propagates(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    stages_dir, output_dir = _prepare_environment(tmp_path, monkeypatch)
    for stage in aggregate_q1.STAGES:
        guard = "FAIL" if stage == "s4" else "PASS"
        _write_stage(stages_dir, stage, status="PASS", score=Decimal("0.9800"), guard=guard)

    artifacts = aggregate_q1.generate_report()

    assert artifacts.summary["status"] == "FAIL"
    assert any(entry["status"] == "FAIL" for entry in artifacts.stages if entry["stage"] == "s4")
    guard_status = (output_dir / "guard_status.txt").read_text(encoding="utf-8").strip()
    assert guard_status == "FAIL"


def test_missing_guard_status_fails(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    stages_dir, output_dir = _prepare_environment(tmp_path, monkeypatch)
    for stage in aggregate_q1.STAGES:
        _write_stage(stages_dir, stage, status="PASS", score=Decimal("0.9800"), guard="PASS")
    (stages_dir / f"s3{aggregate_q1.STAGE_GUARD_SUFFIX}").unlink()

    with pytest.raises(aggregate_q1.AggregationFailure) as excinfo:
        aggregate_q1.generate_report()
    assert excinfo.value.code == "STAGE-GUARD-MISSING"
    assert (output_dir / "guard_status.txt").read_text(encoding="utf-8").strip() == "FAIL"


def test_guard_divergence_detected(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    stages_dir, output_dir = _prepare_environment(tmp_path, monkeypatch)
    for stage in aggregate_q1.STAGES:
        status = "FAIL" if stage == "s2" else "PASS"
        _write_stage(stages_dir, stage, status=status, score=Decimal("0.9800"), guard="PASS")

    with pytest.raises(aggregate_q1.AggregationFailure) as excinfo:
        aggregate_q1.generate_report()
    assert excinfo.value.code == "STAGE-GUARD-DIVERGENCE"
    assert (output_dir / "guard_status.txt").read_text(encoding="utf-8").strip() == "FAIL"
