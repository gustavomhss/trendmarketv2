from __future__ import annotations

import json
from decimal import Decimal
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
    path.write_text(json.dumps(content, indent=2, ensure_ascii=False) + "
", encoding="utf-8")


def test_threshold_validation_rejects_ratio_above_one(tmp_path: Path) -> None:
    data = json.loads(THRESHOLDS_SRC.read_text(encoding="utf-8"))
    data["quorum_ratio_min"] = 1.5
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


def test_boss_report_schema_version_enforced() -> None:
    stages = [
        {
            "stage": "s1",
            "status": "PASS",
            "score": Decimal("1.0"),
            "formatted_score": "1.0000",
            "generated_at": "2024-01-01T00:00:00Z",
        },
        {
            "stage": "s2",
            "status": "FAIL",
            "score": Decimal("0.0"),
            "formatted_score": "0.0000",
            "generated_at": "2024-01-01T00:00:00Z",
        },
    ]

    summary = aggregate_q1.compute_summary(stages)
    report = aggregate_q1.build_report(stages, summary)

    schema = json.loads(Path(BASE_DIR / "schemas" / "q1_boss_report.schema.json").read_text(encoding="utf-8"))
    validator = Draft7Validator(schema)
    validator.validate(report)

    report["schema_version"] = aggregate_q1.SCHEMA_VERSION + 1
    with pytest.raises(ValidationError):
        validator.validate(report)
