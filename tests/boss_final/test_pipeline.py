from __future__ import annotations

import json
from decimal import Decimal
from pathlib import Path

import pytest
from hypothesis import HealthCheck, given, seed, settings as hp_settings
from hypothesis import strategies as st

from scripts.boss_final import aggregate_q1 as pipeline

try:
    hp_settings.register_profile(
        "ci",
        hp_settings(max_examples=50, deadline=None, suppress_health_check=(HealthCheck.too_slow,)),
    )
except ValueError:
    pass


def _stage_entry(stage: str, status: str, score: Decimal) -> dict[str, object]:
    formatted = score.quantize(Decimal("0.0001"))
    return {
        "stage": stage,
        "status": status,
        "score": score,
        "formatted_score": f"{formatted}",
        "generated_at": "2024-01-01T00:00:00Z",
    }


@given(st.lists(st.booleans(), min_size=len(pipeline.STAGES), max_size=len(pipeline.STAGES)))
@hp_settings(profile="ci")
@seed(12345)
def test_compute_summary_propagates_failures(statuses: list[bool]) -> None:
    entries = []
    for stage, ok in zip(pipeline.STAGES, statuses, strict=True):
        score = Decimal("0.98") if ok else Decimal("0.45")
        entries.append(_stage_entry(stage, "PASS" if ok else "FAIL", score))
    summary = pipeline.compute_summary(entries)
    expected_status = "PASS" if all(statuses) else "FAIL"
    assert summary["status"] == expected_status
    failing_expected = len([flag for flag in statuses if not flag])
    assert summary["failing_stages"] == failing_expected
    aggregate = Decimal(summary["aggregate_ratio"])
    expected_ratio = (sum(entry["score"] for entry in entries) / Decimal(len(entries))).quantize(
        Decimal("0.0001")
    )
    assert aggregate == expected_ratio


def test_write_outputs_generates_artifacts(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    stages = [_stage_entry(stage, "PASS", Decimal("0.9720")) for stage in pipeline.STAGES]
    summary = pipeline.compute_summary(stages)
    report = pipeline.build_report(stages, summary)
    bundle_hash = "a" * 64
    report_with_bundle = dict(report)
    report_with_bundle["bundle"] = {"sha256": bundle_hash}
    output_dir = tmp_path / "boss"
    monkeypatch.setattr(pipeline, "OUTPUT_DIR", output_dir)

    pipeline.write_outputs(report_with_bundle, stages, summary, bundle_hash)

    badge = (output_dir / "badge.svg").read_text(encoding="utf-8")
    dag = (output_dir / "dag.svg").read_text(encoding="utf-8")
    guard = (output_dir / "guard_status.txt").read_text(encoding="utf-8")
    pr_comment = (output_dir / "pr_comment.md").read_text(encoding="utf-8")

    assert "Q1 PASS" in badge
    for stage in pipeline.STAGES:
        assert stage.upper() in dag
    assert guard.strip() == "PASS"
    assert bundle_hash in pr_comment


def test_guard_status_reflects_failure(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    stages = [_stage_entry(stage, "PASS", Decimal("0.9720")) for stage in pipeline.STAGES]
    stages[2]["status"] = "FAIL"
    summary = pipeline.compute_summary(stages)
    report = pipeline.build_report(stages, summary)
    bundle_hash = "b" * 64
    report_with_bundle = dict(report)
    report_with_bundle["bundle"] = {"sha256": bundle_hash}
    output_dir = tmp_path / "boss_fail"
    monkeypatch.setattr(pipeline, "OUTPUT_DIR", output_dir)

    pipeline.write_outputs(report_with_bundle, stages, summary, bundle_hash)

    guard = (output_dir / "guard_status.txt").read_text(encoding="utf-8").strip()
    badge = (output_dir / "badge.svg").read_text(encoding="utf-8")

    assert guard == "FAIL"
    assert "Q1 FAIL" in badge


def test_load_stage_missing_file(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    stages_dir = tmp_path / "stages"
    stages_dir.mkdir()
    monkeypatch.setattr(pipeline, "STAGES_DIR", stages_dir)
    guard_path = stages_dir / f"s1{pipeline.STAGE_GUARD_SUFFIX}"
    guard_path.write_text("PASS
", encoding="utf-8")

    with pytest.raises(pipeline.AggregationFailure) as excinfo:
        pipeline.load_stage("s1")
    assert excinfo.value.code == "STAGE-MISSING"
