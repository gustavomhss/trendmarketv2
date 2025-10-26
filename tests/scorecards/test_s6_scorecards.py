from __future__ import annotations

import json
from pathlib import Path

import pytest

from scripts.scorecards import s6_scorecards


FIXTURE_DIR = Path(__file__).resolve().parents[2] / "s6_validation"


def _write_json(path: Path, payload: dict) -> None:
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def test_generate_report_pass(tmp_path: Path) -> None:
    thresholds = json.loads((FIXTURE_DIR / "thresholds.json").read_text(encoding="utf-8"))
    metrics = json.loads((FIXTURE_DIR / "metrics_static.json").read_text(encoding="utf-8"))
    thresholds_path = tmp_path / "thresholds.json"
    metrics_path = tmp_path / "metrics.json"
    _write_json(thresholds_path, thresholds)
    _write_json(metrics_path, metrics)

    report = s6_scorecards.generate_report(threshold_path=thresholds_path, metrics_path=metrics_path)

    assert report["status"] == "PASS"
    assert set(report["metrics"].keys()) == set(s6_scorecards.METRIC_ORDER)
    assert report["summary"] == {"total": 5, "passing": 5, "failing": 0}
    assert Path("out/s6_scorecards/guard_status.txt").read_text(encoding="utf-8").strip() == "PASS"


def test_generate_report_fail_when_threshold_breached(tmp_path: Path) -> None:
    thresholds = json.loads((FIXTURE_DIR / "thresholds.json").read_text(encoding="utf-8"))
    metrics = json.loads((FIXTURE_DIR / "metrics_static.json").read_text(encoding="utf-8"))
    metrics["metrics"]["quorum_ratio"]["observed"] = "0.10"
    thresholds_path = tmp_path / "thresholds.json"
    metrics_path = tmp_path / "metrics.json"
    _write_json(thresholds_path, thresholds)
    _write_json(metrics_path, metrics)

    report = s6_scorecards.generate_report(threshold_path=thresholds_path, metrics_path=metrics_path)

    assert report["status"] == "FAIL"
    assert report["metrics"]["quorum_ratio"]["ok"] is False
    assert report["summary"]["failing"] == 1


def test_bundle_hash_is_canonical(tmp_path: Path) -> None:
    thresholds = json.loads((FIXTURE_DIR / "thresholds.json").read_text(encoding="utf-8"))
    metrics = json.loads((FIXTURE_DIR / "metrics_static.json").read_text(encoding="utf-8"))
    thresholds_path = tmp_path / "thresholds.json"
    metrics_path = tmp_path / "metrics.json"
    _write_json(thresholds_path, thresholds)
    _write_json(metrics_path, metrics)

    report = s6_scorecards.generate_report(threshold_path=thresholds_path, metrics_path=metrics_path)

    expected_material = (
        json.dumps(thresholds, sort_keys=True, ensure_ascii=False, separators=(",", ":"))
        + "\n"
        + json.dumps(metrics, sort_keys=True, ensure_ascii=False, separators=(",", ":"))
        + "\n"
    ).encode("utf-8")
    expected_hash = s6_scorecards.hashlib.sha256(expected_material).hexdigest()
    assert report["bundle_sha256"] == expected_hash


def test_threshold_version_mismatch_raises(tmp_path: Path) -> None:
    thresholds = json.loads((FIXTURE_DIR / "thresholds.json").read_text(encoding="utf-8"))
    thresholds["version"] = 2
    metrics = json.loads((FIXTURE_DIR / "metrics_static.json").read_text(encoding="utf-8"))
    thresholds_path = tmp_path / "thresholds.json"
    metrics_path = tmp_path / "metrics.json"
    _write_json(thresholds_path, thresholds)
    _write_json(metrics_path, metrics)

    with pytest.raises(s6_scorecards.ScorecardError) as exc:
        s6_scorecards.generate_report(threshold_path=thresholds_path, metrics_path=metrics_path)

    assert exc.value.code.startswith("S6-E-SCHEMA")
