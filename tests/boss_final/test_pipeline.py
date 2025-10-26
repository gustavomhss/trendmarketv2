from decimal import Decimal
from pathlib import Path

import pytest
from decimal import Decimal
from pathlib import Path

from hypothesis import HealthCheck, given, seed, strategies as st
from hypothesis import settings as hp_settings

from scripts.boss_final import aggregate_q1 as pipeline

try:
    hp_settings.register_profile(
        "ci",
        hp_settings(max_examples=50, deadline=None, suppress_health_check=(HealthCheck.too_slow,)),
    )
except ValueError:
    pass


def _stage_entry(stage: str, status: str, score: Decimal) -> dict[str, str]:
    formatted = score.quantize(Decimal("0.0001"))
    entry: dict[str, str] = {
        "schema_version": 1,
        "stage": stage,
        "status": status,
        "score": str(score),
        "formatted_score": f"{formatted}",
        "generated_at": "2024-01-01T00:00:00Z",
    }
    if status != "pass":
        entry["on_fail"] = "Investigate pipeline regressions."
    if stage == "s6":
        entry["report_path"] = "out/s6_scorecards"
        entry["bundle_sha256"] = "deadbeef"
    return entry


@given(st.lists(st.booleans(), min_size=len(pipeline.STAGES), max_size=len(pipeline.STAGES)))
@hp_settings(profile="ci")
@seed(12345)
def test_compute_summary_propagates_failures(statuses: list[bool]) -> None:
    stage_entries = []
    scores: list[Decimal] = []
    for stage, ok in zip(pipeline.STAGES, statuses, strict=True):
        score_value = Decimal("1.0") if ok else Decimal("0.5")
        stage_entries.append(_stage_entry(stage, "pass" if ok else "fail", score_value))
        scores.append(score_value)
    summary = pipeline.compute_summary(stage_entries)
    expected_status = "pass" if all(statuses) else "fail"
    assert summary["status"] == expected_status
    assert summary["failing_stages"] == len([flag for flag in statuses if not flag])
    aggregate = Decimal(summary["aggregate_ratio"])
    expected_ratio = sum(scores) / Decimal(len(scores))
    assert aggregate == expected_ratio.quantize(Decimal("0.0001"))


@given(st.lists(st.booleans(), min_size=len(pipeline.STAGES), max_size=len(pipeline.STAGES)))
@hp_settings(profile="ci")
@seed(67890)
def test_guard_status_matches_any_stage_failure(statuses: list[bool], tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    stage_entries = []
    for stage, ok in zip(pipeline.STAGES, statuses, strict=True):
        value = Decimal("0.95") if ok else Decimal("0.40")
        stage_entries.append(_stage_entry(stage, "pass" if ok else "fail", value))
    report = pipeline.build_report(stage_entries)
    output_dir = tmp_path / "boss_matrix"
    monkeypatch.setattr(pipeline, "OUTPUT_DIR", output_dir)

    pipeline.write_outputs(report)

    guard_text = (output_dir / "guard_status.txt").read_text(encoding="utf-8").strip()
    expected = "PASS" if all(statuses) else "FAIL"
    assert guard_text == expected
    badge = (output_dir / "badge.svg").read_text(encoding="utf-8")
    dag = (output_dir / "dag.svg").read_text(encoding="utf-8")
    assert f"Q1 {expected}" in badge
    for stage in pipeline.STAGES:
        assert stage.upper() in dag


def test_write_outputs_generates_artifacts(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    stages = [_stage_entry(stage, "pass", Decimal("0.9820")) for stage in pipeline.STAGES]
    report = pipeline.build_report(stages)
    output_dir = tmp_path / "boss"
    monkeypatch.setattr(pipeline, "OUTPUT_DIR", output_dir)

    pipeline.write_outputs(report)

    badge = (output_dir / "badge.svg").read_text(encoding="utf-8")
    dag = (output_dir / "dag.svg").read_text(encoding="utf-8")
    guard = (output_dir / "guard_status.txt").read_text(encoding="utf-8")

    assert "Q1 PASS" in badge
    for stage in pipeline.STAGES:
        assert stage.upper() in dag
    assert guard == "PASS\n"
    assert (output_dir / "bundle.sha256").read_text(encoding="utf-8").strip()


def test_guard_status_reflects_failure(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    stages = [_stage_entry(stage, "pass", Decimal("0.9820")) for stage in pipeline.STAGES]
    stages[2]["status"] = "fail"
    stages[2]["score"] = str(Decimal("0.1000"))
    stages[2]["formatted_score"] = "0.1000"
    report = pipeline.build_report(stages)
    output_dir = tmp_path / "boss_fail"
    monkeypatch.setattr(pipeline, "OUTPUT_DIR", output_dir)

    pipeline.write_outputs(report)

    badge = (output_dir / "badge.svg").read_text(encoding="utf-8")
    guard = (output_dir / "guard_status.txt").read_text(encoding="utf-8")

    assert "Q1 FAIL" in badge
    assert guard == "FAIL\n"


def test_load_stage_missing_file(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    stages_dir = tmp_path / "stages"
    monkeypatch.setattr(pipeline, "STAGES_DIR", stages_dir)

    with pytest.raises(SystemExit) as excinfo:
        pipeline.load_stage("s1")
    assert "BOSS-E-STAGE-MISSING" in str(excinfo.value)
