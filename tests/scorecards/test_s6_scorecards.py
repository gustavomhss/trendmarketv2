from __future__ import annotations

import json
from decimal import Decimal
from pathlib import Path

import pytest
from hypothesis import HealthCheck, given, seed, settings as hp_settings
from hypothesis import strategies as st

from scripts.scorecards import s6_scorecards as scorecards

try:
    hp_settings.register_profile(
        "ci",
        hp_settings(max_examples=50, deadline=None, suppress_health_check=(HealthCheck.too_slow,)),
    )
except ValueError:
    pass
from scripts.scorecards.s6_scorecards import (
    EPSILON,
    METRIC_DEFINITIONS,
    ScorecardArtifacts,
    ScorecardError,
    compare,
    evaluate_metrics,
    format_value,
)


DECIMAL_RATIO = st.decimals(
    min_value=Decimal("0.1"),
    max_value=Decimal("0.99"),
    places=4,
    allow_nan=False,
    allow_infinity=False,
)

DECIMAL_LATENCY = st.decimals(
    min_value=Decimal("0"),
    max_value=Decimal("120"),
    places=4,
    allow_nan=False,
    allow_infinity=False,
)


def _base_thresholds() -> dict[str, object]:
    return {
        "version": 1,
        "timestamp_utc": "2024-01-01T00:00:00Z",
        "quorum_ratio_min": 0.80,
        "failover_time_p95_s_max": 60.0,
        "staleness_p95_s_max": 30.0,
        "cdc_lag_p95_s_max": 120.0,
        "divergence_pct_max": 1.0,
    }


def _freeze_datetime(monkeypatch: pytest.MonkeyPatch) -> None:
    class FrozenDateTime(datetime):
        @classmethod
        def now(cls, tz: timezone | None = None) -> datetime:
            return datetime(2024, 1, 1, 12, 0, 0, tzinfo=tz or timezone.utc)

def _base_metrics() -> dict[str, object]:
    return {
        "version": 1,
        "timestamp_utc": "2024-01-01T00:00:00Z",
        "quorum_ratio": 0.90,
        "failover_time_p95_s": 12.0,
        "staleness_p95_s": 8.0,
        "cdc_lag_p95_s": 20.0,
        "divergence_pct": 0.4,
    }


def _write_inputs(tmp_path: Path, thresholds: dict[str, object], metrics: dict[str, object]) -> tuple[Path, Path]:
    thresholds_path = tmp_path / "thresholds.json"
    metrics_path = tmp_path / "metrics.json"
    thresholds_path.write_text(json.dumps(thresholds), encoding="utf-8")
    metrics_path.write_text(json.dumps(metrics), encoding="utf-8")
    return thresholds_path, metrics_path


def _freeze_time(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(scorecards, "isoformat_utc", lambda: "2024-01-01T06:00:00Z")


@pytest.fixture
def output_dir(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> Path:
    directory = tmp_path / "out"
    monkeypatch.setattr(scorecards, "OUTPUT_DIR", directory)
    return directory


def test_generate_report_pass_flow(output_dir: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    _freeze_time(monkeypatch)
    thresholds_path, metrics_path = _write_inputs(tmp_path, _base_thresholds(), _base_metrics())

    artifacts = scorecards.generate_report(threshold_path=thresholds_path, metrics_path=metrics_path)

    assert artifacts.report["status"] == "PASS"
    guard_status = (output_dir / "guard_status.txt").read_text(encoding="utf-8").strip()
    assert guard_status == "PASS"
    report = json.loads((output_dir / "report.json").read_text(encoding="utf-8"))
    assert report["schema_version"] == scorecards.SCHEMA_VERSION
    assert report["inputs"]["thresholds"]["version"] == 1
    assert report["bundle"]["sha256"] == artifacts.bundle_sha256

    monkeypatch.setattr(scorecards, "datetime", FrozenDateTime)

def test_generate_report_fail_flow_sets_guard(output_dir: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    _freeze_time(monkeypatch)
    thresholds = _base_thresholds()
    metrics = _base_metrics()
    metrics["failover_time_p95_s"] = thresholds["failover_time_p95_s_max"] + 10
    thresholds_path, metrics_path = _write_inputs(tmp_path, thresholds, metrics)

    artifacts = scorecards.generate_report(threshold_path=thresholds_path, metrics_path=metrics_path)

    assert artifacts.report["status"] == "FAIL"
    guard_status = (output_dir / "guard_status.txt").read_text(encoding="utf-8").strip()
    assert guard_status == "FAIL"
    markdown = (output_dir / "report.md").read_text(encoding="utf-8")
    assert "❌ FAIL" in markdown


@given(target=DECIMAL_RATIO)
@hp_settings(profile="ci")
@seed(12345)
def test_evaluate_metrics_respects_epsilon_gte(target: Decimal) -> None:
    thresholds = _base_thresholds()
    metrics = _base_metrics()
    thresholds["quorum_ratio_min"] = float(target)
    metrics["quorum_ratio"] = float(target - (scorecards.EPSILON / 2))

    results = scorecards.evaluate_metrics(thresholds, metrics)
    quorum = next(result for result in results if result.spec.key == "quorum_ratio")
    assert quorum.ok

    metrics["quorum_ratio"] = float(target - (scorecards.EPSILON * 2))
    results = scorecards.evaluate_metrics(thresholds, metrics)
    quorum = next(result for result in results if result.spec.key == "quorum_ratio")
    assert not quorum.ok


@given(target=DECIMAL_LATENCY)
@hp_settings(profile="ci")
@seed(12345)
def test_evaluate_metrics_respects_epsilon_lte(target: Decimal) -> None:
    thresholds = _base_thresholds()
    metrics = _base_metrics()
    thresholds["failover_time_p95_s_max"] = float(target)
    metrics["failover_time_p95_s"] = float(target + (scorecards.EPSILON / 2))

    results = scorecards.evaluate_metrics(thresholds, metrics)
    failover = next(result for result in results if result.spec.key == "failover_time_p95_s")
    assert failover.ok

    metrics["failover_time_p95_s"] = float(target + (scorecards.EPSILON * 2))
    results = scorecards.evaluate_metrics(thresholds, metrics)
    failover = next(result for result in results if result.spec.key == "failover_time_p95_s")
    assert not failover.ok


@given(
    target=DECIMAL_RATIO,
    measurement_delta=st.decimals(min_value=Decimal("0"), max_value=Decimal("0.3"), places=4, allow_nan=False),
    relax=st.decimals(min_value=Decimal("0"), max_value=Decimal("0.1"), places=4, allow_nan=False),
    tighten=st.decimals(min_value=Decimal("0"), max_value=Decimal("0.1"), places=4, allow_nan=False),
)
@hp_settings(profile="ci")
@seed(12345)
def test_metamorphic_relax_and_tighten_gte(
    target: Decimal,
    measurement_delta: Decimal,
    relax: Decimal,
    tighten: Decimal,
) -> None:
    thresholds = _base_thresholds()
    metrics = _base_metrics()
    thresholds["quorum_ratio_min"] = float(target)
    measurement = max(Decimal("0"), target - measurement_delta)
    metrics["quorum_ratio"] = float(measurement)

    base = scorecards.evaluate_metrics(thresholds, metrics)
    quorum = next(result for result in base if result.spec.key == "quorum_ratio")

    thresholds_relaxed = dict(thresholds)
    thresholds_relaxed["quorum_ratio_min"] = float(target - relax)
    relaxed = scorecards.evaluate_metrics(thresholds_relaxed, metrics)
    relaxed_quorum = next(result for result in relaxed if result.spec.key == "quorum_ratio")
    if quorum.ok:
        assert relaxed_quorum.ok

    thresholds_tight = dict(thresholds)
    thresholds_tight["quorum_ratio_min"] = float(target + tighten)
    tightened = scorecards.evaluate_metrics(thresholds_tight, metrics)
    tightened_quorum = next(result for result in tightened if result.spec.key == "quorum_ratio")
    if not quorum.ok:
        assert not tightened_quorum.ok


@given(
    target=DECIMAL_LATENCY,
    measurement_delta=st.decimals(min_value=Decimal("0"), max_value=Decimal("30"), places=4, allow_nan=False),
    relax=st.decimals(min_value=Decimal("0"), max_value=Decimal("20"), places=4, allow_nan=False),
    tighten=st.decimals(min_value=Decimal("0"), max_value=Decimal("20"), places=4, allow_nan=False),
)
@hp_settings(profile="ci")
@seed(12345)
def test_metamorphic_relax_and_tighten_lte(
    target: Decimal,
    measurement_delta: Decimal,
    relax: Decimal,
    tighten: Decimal,
) -> None:
    thresholds = _base_thresholds()
    metrics = _base_metrics()
    thresholds["failover_time_p95_s_max"] = float(target)
    measurement = target + measurement_delta
    metrics["failover_time_p95_s"] = float(measurement)

    base = scorecards.evaluate_metrics(thresholds, metrics)
    failover = next(result for result in base if result.spec.key == "failover_time_p95_s")

    thresholds_relaxed = dict(thresholds)
    thresholds_relaxed["failover_time_p95_s_max"] = float(target + relax)
    relaxed = scorecards.evaluate_metrics(thresholds_relaxed, metrics)
    relaxed_failover = next(result for result in relaxed if result.spec.key == "failover_time_p95_s")
    if failover.ok:
        assert relaxed_failover.ok

    thresholds_tight = dict(thresholds)
    thresholds_tight["failover_time_p95_s_max"] = float(max(Decimal("0"), target - tighten))
    tightened = scorecards.evaluate_metrics(thresholds_tight, metrics)
    tightened_failover = next(result for result in tightened if result.spec.key == "failover_time_p95_s")
    if not failover.ok:
        assert not tightened_failover.ok


def test_metric_formatting_helpers() -> None:
    spec = scorecards.METRIC_SPECS[0]
    result = scorecards.MetricResult(spec=spec, observed=Decimal("0.91234"), target=Decimal("0.95000"), ok=False)
    assert result.formatted_observed() == "0.9123"
    assert result.formatted_target() == "0.9500"
    assert result.status_text() == "FAIL"


def test_idempotent_reruns(output_dir: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    _freeze_time(monkeypatch)
    thresholds_path, metrics_path = _write_inputs(tmp_path, _base_thresholds(), _base_metrics())

    first = scorecards.generate_report(threshold_path=thresholds_path, metrics_path=metrics_path)
    outputs_first = {
        path.name: path.read_text(encoding="utf-8")
        for path in sorted(output_dir.iterdir())
    }

    second = scorecards.generate_report(threshold_path=thresholds_path, metrics_path=metrics_path)
    outputs_second = {
        path.name: path.read_text(encoding="utf-8")
        for path in sorted(output_dir.iterdir())
    }
@given(target=st.integers(-10, 10))
def test_compare_gte_respects_epsilon_boundary(target: int) -> None:
    target_decimal = Decimal(target)
    within_epsilon = target_decimal - (EPSILON / 2)
    assert compare(within_epsilon, target_decimal, "gte")

    beyond_epsilon = target_decimal - (EPSILON * 2)
    assert not compare(beyond_epsilon, target_decimal, "gte")


@given(target=st.integers(-10, 10))
def test_compare_lte_respects_epsilon_boundary(target: int) -> None:
    target_decimal = Decimal(target)
    within_epsilon = target_decimal + (EPSILON / 2)
    assert compare(within_epsilon, target_decimal, "lte")

    beyond_epsilon = target_decimal + (EPSILON * 2)
    assert not compare(beyond_epsilon, target_decimal, "lte")


@given(value=DECIMAL_VALUES)
def test_compare_rejects_unknown_operator(value: Decimal) -> None:
    with pytest.raises(ScorecardError) as exc:
        compare(value, value, "unknown")
    assert exc.value.code == "S6-E-COMPARATOR"


@pytest.mark.parametrize(
    "value, unit, expected",
    [
        (Decimal("99.94"), "percent", "99.9%"),
        (Decimal("0.23456"), "ratio", "0.2346"),
        (Decimal("12.3456"), "seconds", "12.346s"),
        (Decimal("5"), "other", "5"),
    ],
)
def test_format_value_canonical(value: Decimal, unit: str, expected: str) -> None:
    assert format_value(value, unit) == expected


def _write_inputs(tmp_path: Path) -> tuple[Path, Path]:
    thresholds = {
        "version": 1,
        "timestamp_utc": "2024-01-01T06:00:00Z",
        "quorum_ratio": 0.95,
        "failover_time_p95_s": 10.0,
        "staleness_p95_s": 12.0,
        "cdc_lag_p95_s": 20.0,
        "divergence_pct": 0.5,
    }
    metrics = {
        "version": 1,
        "timestamp_utc": "2024-01-01T05:50:00Z",
        "quorum_ratio": 0.96,
        "failover_time_p95_s": 8.0,
        "staleness_p95_s": 10.0,
        "cdc_lag_p95_s": 18.0,
        "divergence_pct": 0.4,
    }
    thresholds_path = tmp_path / "thresholds.json"
    metrics_path = tmp_path / "metrics.json"
    thresholds_path.write_text(json.dumps(thresholds), encoding="utf-8")
    metrics_path.write_text(json.dumps(metrics), encoding="utf-8")
    return thresholds_path, metrics_path


def test_evaluate_metrics_requires_all_fields() -> None:
    thresholds = {definition.key: 1 for definition in METRIC_DEFINITIONS}
    thresholds.update({"version": 1, "timestamp_utc": "2024-01-01T00:00:00Z"})
    metrics = {definition.key: 1 for definition in METRIC_DEFINITIONS[1:]}  # omit first key
    metrics.update({"version": 1, "timestamp_utc": "2024-01-01T00:00:00Z"})

    with pytest.raises(ScorecardError) as exc:
        evaluate_metrics(thresholds, metrics)
    assert exc.value.code == "S6-E-MISSING-METRIC"


def _valid_report_payload() -> dict[str, object]:
    return {
        "schema_version": 1,
        "timestamp_utc": "2024-01-01T00:00:00Z",
        "status": "PASS",
        "metrics": {
            "quorum_ratio": {"observed": 0.9, "target": 0.9, "ok": True},
            "failover_time_p95_s": {"observed": 7.0, "target": 10.0, "ok": True},
            "staleness_p95_s": {"observed": 5.0, "target": 10.0, "ok": True},
            "cdc_lag_p95_s": {"observed": 15.0, "target": 30.0, "ok": True},
            "divergence_pct": {"observed": 0.5, "target": 1.0, "ok": True},
        },
        "inputs": {
            "thresholds": {"version": 1, "timestamp_utc": "2024-01-01T00:00:00Z"},
            "metrics": {"version": 1, "timestamp_utc": "2024-01-01T00:00:00Z"},
        },
        "bundle": {"sha256": "a" * 64},
    }


def test_load_json_rejects_metrics_outside_bounds(tmp_path: Path) -> None:
    metrics_path = tmp_path / "metrics.json"
    metrics_payload = {
        "version": 1,
        "timestamp_utc": "2024-01-01T00:00:00Z",
        "quorum_ratio": 1.5,
        "failover_time_p95_s": 7.0,
        "staleness_p95_s": 5.0,
        "cdc_lag_p95_s": 15.0,
        "divergence_pct": 0.5,
    }
    metrics_path.write_text(json.dumps(metrics_payload), encoding="utf-8")

    with pytest.raises(RuntimeError) as exc:
        scorecards.load_json(metrics_path, "metrics")

    assert "SCHEMA" in str(exc.value)


def test_load_json_enforces_report_schema_version_const(tmp_path: Path) -> None:
    report_path = tmp_path / "report.json"
    valid_report = _valid_report_payload()
    report_path.write_text(json.dumps(valid_report), encoding="utf-8")

    loaded = scorecards.load_json(report_path, "report")
    assert loaded["schema_version"] == 1

    invalid_report = {**valid_report, "schema_version": 2}
    report_path.write_text(json.dumps(invalid_report), encoding="utf-8")

    with pytest.raises(RuntimeError) as exc:
        scorecards.load_json(report_path, "report")

    assert "SCHEMA" in str(exc.value)


def test_generate_report_is_idempotent(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    output_dir = tmp_path / "out"
    monkeypatch.setattr(scorecards, "OUTPUT_DIR", output_dir)
    _freeze_datetime(monkeypatch)
    thresholds_path, metrics_path = _write_inputs(tmp_path)

    artifacts_first: ScorecardArtifacts = scorecards.generate_report(thresholds_path, metrics_path)
    markdown_first = (output_dir / "report.md").read_text(encoding="utf-8")
    bundle_hash_first = artifacts_first.bundle_sha256

    artifacts_second: ScorecardArtifacts = scorecards.generate_report(thresholds_path, metrics_path)
    markdown_second = (output_dir / "report.md").read_text(encoding="utf-8")

    assert artifacts_first.report == artifacts_second.report
    assert artifacts_second.bundle_sha256 == bundle_hash_first
    assert markdown_first == markdown_second
    assert (output_dir / "bundle.sha256").read_text(encoding="utf-8").strip() == bundle_hash_first
    assert (output_dir / "guard_status.txt").read_text(encoding="utf-8").strip() == "PASS"

    assert first.bundle_sha256 == second.bundle_sha256
    assert outputs_first == outputs_second


def test_missing_thresholds_file_raises(tmp_path: Path, output_dir: Path) -> None:
    metrics_path = _write_inputs(tmp_path, _base_thresholds(), _base_metrics())[1]
    with pytest.raises(scorecards.ScorecardError) as excinfo:
        scorecards.generate_report(threshold_path=tmp_path / "missing.json", metrics_path=metrics_path)
    assert excinfo.value.code == "S6-E-MISSING"
    assert (output_dir / "guard_status.txt").read_text(encoding="utf-8").strip() == "FAIL"


def test_schema_violation_raises(tmp_path: Path, output_dir: Path) -> None:
    thresholds = _base_thresholds()
    thresholds.pop("quorum_ratio_min")
    thresholds_path, metrics_path = _write_inputs(tmp_path, thresholds, _base_metrics())
def test_generate_report_schema_violation(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    output_dir = tmp_path / "out"
    monkeypatch.setattr(scorecards, "OUTPUT_DIR", output_dir)
    thresholds_path, metrics_path = _write_inputs(tmp_path)
    thresholds_path.write_text(json.dumps({"version": 1}), encoding="utf-8")

    with pytest.raises(scorecards.ScorecardError) as excinfo:
        scorecards.generate_report(threshold_path=thresholds_path, metrics_path=metrics_path)
    assert excinfo.value.code == "S6-E-SCHEMA"
    assert (output_dir / "guard_status.txt").read_text(encoding="utf-8").strip() == "FAIL"


def test_invalid_encoding_raises(tmp_path: Path, output_dir: Path) -> None:
    thresholds_path = tmp_path / "thresholds.json"
    metrics_path = _write_inputs(tmp_path, _base_thresholds(), _base_metrics())[1]
    thresholds_path.write_bytes(b"ÿþinvalid")

    with pytest.raises(scorecards.ScorecardError) as excinfo:
        scorecards.generate_report(threshold_path=thresholds_path, metrics_path=metrics_path)
    assert excinfo.value.code == "S6-E-ENCODING"
    assert (output_dir / "guard_status.txt").read_text(encoding="utf-8").strip() == "FAIL"
