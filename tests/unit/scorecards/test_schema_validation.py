from __future__ import annotations

import json
from pathlib import Path

import pytest

jsonschema = pytest.importorskip("jsonschema")
Draft7Validator = jsonschema.Draft7Validator
ValidationError = jsonschema.ValidationError

from scripts.boss_final import aggregate_q1
from scripts.scorecards import s6_scorecards

BASE_DIR = Path(__file__).resolve().parents[3]
THRESHOLDS_SRC = BASE_DIR / "s6_validation" / "thresholds.json"
METRICS_SRC = BASE_DIR / "s6_validation" / "metrics_static.json"


def _write_json(path: Path, content: dict) -> None:
    path.write_text(json.dumps(content, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


def test_threshold_validation_rejects_ratio_above_one(tmp_path: Path) -> None:
    data = json.loads(THRESHOLDS_SRC.read_text(encoding="utf-8"))
    data["quorum_ratio"] = 1.5
    test_path = tmp_path / "thresholds.json"
    _write_json(test_path, data)

    with pytest.raises(s6_scorecards.ScorecardError) as excinfo:
        s6_scorecards.load_json(test_path, "thresholds")

    assert excinfo.value.code == "S6-E-SCHEMA"


def test_threshold_validation_requires_timestamp(tmp_path: Path) -> None:
    data = json.loads(THRESHOLDS_SRC.read_text(encoding="utf-8"))
    data.pop("timestamp_utc")
    test_path = tmp_path / "thresholds.json"
    _write_json(test_path, data)

    with pytest.raises(s6_scorecards.ScorecardError) as excinfo:
        s6_scorecards.load_json(test_path, "thresholds")

    assert excinfo.value.code == "S6-E-SCHEMA"


def test_scorecard_report_schema_version_enforced(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    thresholds_path = tmp_path / "thresholds.json"
    metrics_path = tmp_path / "metrics.json"
    thresholds_path.write_text(THRESHOLDS_SRC.read_text(encoding="utf-8"), encoding="utf-8")
    metrics_path.write_text(METRICS_SRC.read_text(encoding="utf-8"), encoding="utf-8")

    output_dir = tmp_path / "out"
    monkeypatch.setattr(s6_scorecards, "OUTPUT_DIR", output_dir)
    monkeypatch.setattr(s6_scorecards, "isoformat_utc", lambda: "2024-01-01T06:00:00Z")

    artifacts = s6_scorecards.generate_report(threshold_path=thresholds_path, metrics_path=metrics_path)
    report = artifacts.report

    schema = json.loads(Path(s6_scorecards.SCHEMA_FILES["report"]).read_text(encoding="utf-8"))
    validator = Draft7Validator(schema)
    validator.validate(report)

    report["schema_version"] = s6_scorecards.SCHEMA_VERSION + 1
    with pytest.raises(ValidationError):
        validator.validate(report)


def _write_stage_bundle(root: Path, stage: str) -> None:
    stage_dir = root / stage
    stage_dir.mkdir(parents=True, exist_ok=True)
    variants = {
        "primary": {"status": "PASS", "notes": "primary ok"},
        "clean": {"status": "PASS", "notes": "clean ok"},
    }
    for variant, payload in variants.items():
        variant_dir = stage_dir / variant
        variant_dir.mkdir(parents=True, exist_ok=True)
        variant_payload = {
            "stage": stage,
            "variant": variant,
            "status": payload["status"],
            "notes": payload["notes"],
            "timestamp_utc": "2024-01-01T00:00:00Z",
            "checks": [],
        }
        (variant_dir / "result.json").write_text(
            json.dumps(variant_payload, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
        )
        (variant_dir / "guard_status.txt").write_text("PASS\n", encoding="utf-8")
        (variant_dir / "bundle.sha256").write_text("00" * 32 + "\n", encoding="utf-8")
    summary_payload = {
        "stage": stage,
        "status": "PASS",
        "notes": "primary:PASS primary ok | clean:PASS clean ok",
        "variants": {variant: {"status": info["status"], "notes": info["notes"]} for variant, info in variants.items()},
        "timestamp_utc": "2024-01-01T00:05:00Z",
    }
    (stage_dir / "summary.json").write_text(
        json.dumps(summary_payload, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )
    (stage_dir / "guard_status.txt").write_text("PASS\n", encoding="utf-8")


def test_boss_report_schema_version_enforced(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    stages_dir = tmp_path / "stages"
    for stage in aggregate_q1.STAGES:
        _write_stage_bundle(stages_dir, stage)

    monkeypatch.setattr(aggregate_q1, "OUTPUT_DIR", tmp_path)
    monkeypatch.setattr(aggregate_q1, "STAGES_DIR", stages_dir)

    artifacts = aggregate_q1.aggregate("v1.0.0")
    schema = json.loads(Path(BASE_DIR / "schemas" / "q1_boss_report.schema.json").read_text(encoding="utf-8"))
    validator = Draft7Validator(schema)
    validator.validate(artifacts.report)

    artifacts.report["schema_version"] = aggregate_q1.SCHEMA_VERSION + 1
    with pytest.raises(ValidationError):
        validator.validate(artifacts.report)
