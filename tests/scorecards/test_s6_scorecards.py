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
import hashlib
import json
from decimal import Decimal
from pathlib import Path

import pytest
from hypothesis import HealthCheck, Phase, given, settings
from hypothesis import strategies as st

from scripts.scorecards import s6_scorecards

settings.register_profile(
    "ci",
    settings(
        max_examples=50,
        suppress_health_check=(HealthCheck.too_slow,),
        phases=(Phase.explicit, Phase.reuse, Phase.generate),
    ),
)
settings.load_profile("ci")


def _base_thresholds() -> dict[str, object]:
    return {
        "schema": "trendmarketv2.sprint6.thresholds",
        "schema_version": 2,
        "timestamp_utc": "2024-01-01T00:00:00Z",
        "quorum_ratio": 0.9,
        "failover_time_p95_s": 10.0,
        "staleness_p95_s": 12.0,
        "cdc_lag_p95_s": 30.0,
        "divergence_pct": 1.0,
    }


def _base_metrics() -> dict[str, object]:
    return {
        "schema": "trendmarketv2.sprint6.metrics",
        "schema_version": 2,
        "timestamp_utc": "2024-01-01T00:00:00Z",
        "quorum_ratio": 0.95,
        "failover_time_p95_s": 6.0,
        "staleness_p95_s": 8.0,
        "cdc_lag_p95_s": 12.0,
        "divergence_pct": 0.4,
    }


@pytest.fixture
def output_dir(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> Path:
    directory = tmp_path / "out"
    monkeypatch.setattr(s6_scorecards, "OUTPUT_DIR", directory)
    return directory


@pytest.fixture
def inputs(tmp_path: Path) -> tuple[Path, Path]:
    thresholds_path = tmp_path / "thresholds.json"
    metrics_path = tmp_path / "metrics.json"
    thresholds_path.write_text(json.dumps(_base_thresholds()), encoding="utf-8")
    metrics_path.write_text(json.dumps(_base_metrics()), encoding="utf-8")
    return thresholds_path, metrics_path


def _freeze_time(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(s6_scorecards, "isoformat_utc", lambda: "2024-01-01T06:00:00Z")


def test_generate_report_pass_flow(output_dir: Path, inputs: tuple[Path, Path], monkeypatch: pytest.MonkeyPatch) -> None:
    _freeze_time(monkeypatch)
    thresholds_path, metrics_path = inputs

    artifacts = s6_scorecards.generate_report(threshold_path=thresholds_path, metrics_path=metrics_path)

    assert artifacts.report["status"] == "PASS"
    guard_status = (output_dir / "guard_status.txt").read_text(encoding="utf-8").strip()
    assert guard_status == "PASS"

    report = json.loads((output_dir / "report.json").read_text(encoding="utf-8"))
    assert report["schema_version"] == s6_scorecards.SCHEMA_VERSION
    assert report["schema"] == s6_scorecards.REPORT_SCHEMA
    assert report["inputs"]["thresholds"]["schema_version"] == 2
    assert report["inputs"]["metrics"]["schema_version"] == 2
    assert report["bundle"]["sha256"] == artifacts.bundle_sha256


def test_generate_report_fail_flow_sets_guard(output_dir: Path, inputs: tuple[Path, Path], monkeypatch: pytest.MonkeyPatch) -> None:
    _freeze_time(monkeypatch)
    thresholds_path, metrics_path = inputs
    metrics_payload = json.loads(metrics_path.read_text(encoding="utf-8"))
    metrics_payload["failover_time_p95_s"] = 40.0
    metrics_path.write_text(json.dumps(metrics_payload), encoding="utf-8")

    artifacts = s6_scorecards.generate_report(threshold_path=thresholds_path, metrics_path=metrics_path)

    assert artifacts.report["status"] == "FAIL"
    guard_status = (output_dir / "guard_status.txt").read_text(encoding="utf-8").strip()
    assert guard_status == "FAIL"


@given(target=st.decimals(min_value=Decimal("0.7"), max_value=Decimal("0.99"), places=4))
def test_evaluate_metrics_respects_epsilon_gte(target: Decimal) -> None:
    thresholds = _base_thresholds()
    metrics = _base_metrics()
    thresholds["quorum_ratio"] = float(target)

    metrics["quorum_ratio"] = float(target - (s6_scorecards.EPSILON / 2))
    result = s6_scorecards.evaluate_metrics(thresholds, metrics)
    quorum = next(item for item in result if item.definition.key == "quorum_ratio")
    assert quorum.ok

    metrics["quorum_ratio"] = float(target - (s6_scorecards.EPSILON * 2))
    result = s6_scorecards.evaluate_metrics(thresholds, metrics)
    quorum = next(item for item in result if item.definition.key == "quorum_ratio")
    assert not quorum.ok


@given(target=st.decimals(min_value=Decimal("1"), max_value=Decimal("120"), places=3))
def test_evaluate_metrics_respects_epsilon_lte(target: Decimal) -> None:
    thresholds = _base_thresholds()
    metrics = _base_metrics()
    thresholds["failover_time_p95_s"] = float(target)

    metrics["failover_time_p95_s"] = float(target + (s6_scorecards.EPSILON / 2))
    result = s6_scorecards.evaluate_metrics(thresholds, metrics)
    failover = next(item for item in result if item.definition.key == "failover_time_p95_s")
    assert failover.ok

    metrics["failover_time_p95_s"] = float(target + (s6_scorecards.EPSILON * 2))
    result = s6_scorecards.evaluate_metrics(thresholds, metrics)
    failover = next(item for item in result if item.definition.key == "failover_time_p95_s")
    assert not failover.ok


@given(
    measurement=st.decimals(min_value=Decimal("0.5"), max_value=Decimal("0.99"), places=4),
    relax=st.decimals(min_value=Decimal("0"), max_value=Decimal("0.1"), places=4),
    tighten=st.decimals(min_value=Decimal("0"), max_value=Decimal("0.1"), places=4),
)
def test_metamorphic_relax_tighten_gte(measurement: Decimal, relax: Decimal, tighten: Decimal) -> None:
    thresholds = _base_thresholds()
    metrics = _base_metrics()
    thresholds["quorum_ratio"] = float(measurement)
    metrics["quorum_ratio"] = float(measurement)

    base = s6_scorecards.evaluate_metrics(thresholds, metrics)
    quorum = next(item for item in base if item.definition.key == "quorum_ratio")

    relaxed_thresholds = dict(thresholds)
    relaxed_thresholds["quorum_ratio"] = float(max(Decimal("0"), measurement - relax))
    relaxed = s6_scorecards.evaluate_metrics(relaxed_thresholds, metrics)
    relaxed_quorum = next(item for item in relaxed if item.definition.key == "quorum_ratio")
    if quorum.ok:
        assert relaxed_quorum.ok

    tightened_thresholds = dict(thresholds)
    tightened_thresholds["quorum_ratio"] = float(measurement + tighten)
    tightened = s6_scorecards.evaluate_metrics(tightened_thresholds, metrics)
    tightened_quorum = next(item for item in tightened if item.definition.key == "quorum_ratio")
    if not quorum.ok:
        assert not tightened_quorum.ok


def test_idempotent_reruns(output_dir: Path, inputs: tuple[Path, Path], monkeypatch: pytest.MonkeyPatch) -> None:
    _freeze_time(monkeypatch)
    thresholds_path, metrics_path = inputs
    first = s6_scorecards.generate_report(threshold_path=thresholds_path, metrics_path=metrics_path)
    first_outputs = {path.name: path.read_text(encoding="utf-8") for path in sorted(output_dir.iterdir())}

    second = s6_scorecards.generate_report(threshold_path=thresholds_path, metrics_path=metrics_path)
    second_outputs = {path.name: path.read_text(encoding="utf-8") for path in sorted(output_dir.iterdir())}

    assert first.bundle_sha256 == second.bundle_sha256
    assert first_outputs == second_outputs


def test_missing_metric_raises(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    _freeze_time(monkeypatch)
    thresholds = _base_thresholds()
    metrics = _base_metrics()
    metrics.pop("cdc_lag_p95_s")
    thresholds_path = tmp_path / "thresholds.json"
    metrics_path = tmp_path / "metrics.json"
    thresholds_path.write_text(json.dumps(thresholds), encoding="utf-8")
    metrics_path.write_text(json.dumps(metrics), encoding="utf-8")

    with pytest.raises(s6_scorecards.ScorecardError) as excinfo:
        s6_scorecards.generate_report(threshold_path=thresholds_path, metrics_path=metrics_path)
    assert excinfo.value.code == "S6-E-SCHEMA"


def test_missing_threshold_raises(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    _freeze_time(monkeypatch)
    thresholds = _base_thresholds()
    metrics = _base_metrics()
    thresholds.pop("quorum_ratio")
    thresholds_path = tmp_path / "thresholds.json"
    metrics_path = tmp_path / "metrics.json"
    thresholds_path.write_text(json.dumps(thresholds), encoding="utf-8")
    metrics_path.write_text(json.dumps(metrics), encoding="utf-8")

    with pytest.raises(s6_scorecards.ScorecardError) as excinfo:
        s6_scorecards.generate_report(threshold_path=thresholds_path, metrics_path=metrics_path)
    assert excinfo.value.code == "S6-E-SCHEMA"


def test_load_json_schema_violation(tmp_path: Path) -> None:
    metrics_path = tmp_path / "metrics.json"
    metrics_path.write_text(
        json.dumps(
            {
                "schema": "trendmarketv2.sprint6.metrics",
                "schema_version": 2,
                "timestamp_utc": "2024-01-01T00:00:00Z",
                "quorum_ratio": 1.5,
                "failover_time_p95_s": 1.0,
                "staleness_p95_s": 1.0,
                "cdc_lag_p95_s": 1.0,
                "divergence_pct": 1.0,
            }
        ),
        encoding="utf-8",
    )
    with pytest.raises(s6_scorecards.ScorecardError) as excinfo:
        s6_scorecards.load_json(metrics_path, "metrics")
    assert excinfo.value.code == "S6-E-SCHEMA"


def test_load_json_encoding_violation(tmp_path: Path) -> None:
    path = tmp_path / "metrics.json"
    path.write_bytes(b"\xff\xfe\x00\x00")
    with pytest.raises(s6_scorecards.ScorecardError) as excinfo:
        s6_scorecards.load_json(path, "metrics")
    assert excinfo.value.code == "S6-E-ENCODING"


def test_compare_invalid_operator() -> None:
    value = Decimal("1")
    with pytest.raises(s6_scorecards.ScorecardError) as excinfo:
        s6_scorecards.compare(value, value, "neq")
    assert excinfo.value.code == "S6-E-COMPARATOR"


@pytest.mark.parametrize(
    "value, unit, expected",
    [
        (Decimal("0.91234"), "ratio", "0.9123"),
        (Decimal("12.3456"), "seconds", "12.346s"),
        (Decimal("0.4"), "percent", "0.4%"),
        (Decimal("7"), "unknown", "7"),
    ],
)
def test_format_value(value: Decimal, unit: str, expected: str) -> None:
    assert s6_scorecards.format_value(value, unit) == expected


def test_render_pr_comment_contains_status(output_dir: Path, inputs: tuple[Path, Path], monkeypatch: pytest.MonkeyPatch) -> None:
    _freeze_time(monkeypatch)
    thresholds_path, metrics_path = inputs
    artifacts = s6_scorecards.generate_report(threshold_path=thresholds_path, metrics_path=metrics_path)
    comment = (output_dir / "pr_comment.md").read_text(encoding="utf-8")
    assert artifacts.report["status"] in comment
    assert artifacts.bundle_sha256 in comment


def test_bundle_sha_matches_manual(inputs: tuple[Path, Path]) -> None:
    thresholds_path, metrics_path = inputs
    thresholds = json.loads(thresholds_path.read_text(encoding="utf-8"))
    metrics = json.loads(metrics_path.read_text(encoding="utf-8"))
    expected = s6_scorecards.compute_bundle_sha(thresholds, metrics)
    canonical = (
        json.dumps(thresholds, sort_keys=True, ensure_ascii=False, separators=(",", ":"))
        + "\n"
        + json.dumps(metrics, sort_keys=True, ensure_ascii=False, separators=(",", ":"))
        + "\n"
    )
    manual = hashlib.sha256(canonical.encode("utf-8")).hexdigest()
    assert expected == manual
