from pathlib import Path

import pytest
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


def _payload(stage: str, status: str, notes: str) -> pipeline.StagePayload:
    raw = {
        "schema_version": pipeline.SCHEMA_VERSION,
        "stage": stage,
        "status": status,
        "notes": notes,
        "checks": [
            {
                "name": "sanity",
                "status": status,
                "detail": f"Stage {stage} returned {status}",
            }
        ],
        "metadata": {"stage": stage},
    }
    return pipeline.StagePayload(stage=stage, status=status, notes=notes, raw=raw)


@given(st.lists(st.booleans(), min_size=len(pipeline.STAGES), max_size=len(pipeline.STAGES)))
@hp_settings(profile="ci")
@seed(12345)
def test_build_report_reflects_failures(statuses: list[bool]) -> None:
    stage_payloads: list[pipeline.StagePayload] = []
    for stage, ok in zip(pipeline.STAGES, statuses, strict=True):
        status = "PASS" if ok else "FAIL"
        note = "Checks verdes" if ok else "Revisar regressões"
        stage_payloads.append(_payload(stage, status, note))

    report = pipeline.build_report(stage_payloads)

    expected_status = "PASS" if all(statuses) else "FAIL"
    assert report["status"] == expected_status

    for payload in stage_payloads:
        sprint = report["sprints"][payload.stage]
        assert sprint["status"] == payload.status
        assert sprint["notes"] == payload.notes


def test_write_outputs_generates_artifacts(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    stage_payloads = [_payload(stage, "PASS", f"{stage} ok") for stage in pipeline.STAGES]
    report = pipeline.build_report(stage_payloads)
    output_dir = tmp_path / "boss"
    monkeypatch.setattr(pipeline, "OUTPUT_DIR", output_dir)

    bundle_hash = pipeline.write_outputs(report, stage_payloads)

    badge = (output_dir / "badge.svg").read_text(encoding="utf-8")
    dag = (output_dir / "dag.svg").read_text(encoding="utf-8")
    guard = (output_dir / "guard_status.txt").read_text(encoding="utf-8")
    bundle = (output_dir / "bundle.sha256").read_text(encoding="utf-8").strip()

    assert "Q1 PASS" in badge
    for stage in pipeline.STAGES:
        assert stage.upper() in dag
    assert guard == "PASS\n"
    assert bundle == bundle_hash


def test_guard_status_reflects_failure(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    stage_payloads = [_payload(stage, "PASS", f"{stage} ok") for stage in pipeline.STAGES]
    failing_stage = pipeline.STAGES[2]
    stage_payloads[2] = _payload(failing_stage, "FAIL", "Investigate pipeline regressions.")
    report = pipeline.build_report(stage_payloads)
    output_dir = tmp_path / "boss_fail"
    monkeypatch.setattr(pipeline, "OUTPUT_DIR", output_dir)

    pipeline.write_outputs(report, stage_payloads)

    badge = (output_dir / "badge.svg").read_text(encoding="utf-8")
    guard = (output_dir / "guard_status.txt").read_text(encoding="utf-8")

    assert "Q1 FAIL" in badge
    assert guard == "FAIL\n"


def test_load_stage_missing_file(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    stages_dir = tmp_path / "stages"
    monkeypatch.setattr(pipeline, "STAGES_DIR", stages_dir)

    with pytest.raises(SystemExit) as excinfo:
        pipeline.load_stage("s1")
    assert "BOSS-E-STAGE-RESULT-MISSING" in str(excinfo.value)
