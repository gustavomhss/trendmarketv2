import json
from dataclasses import replace
from decimal import Decimal
from pathlib import Path
import datetime as dt

import pytest
from hypothesis import given, seed, strategies as st
from hypothesis import HealthCheck
from hypothesis import settings as hp_settings

from scripts.scorecards import s6_scorecards as scorecards

try:
    hp_settings.register_profile(
        "ci",
        hp_settings(max_examples=50, deadline=None, suppress_health_check=(HealthCheck.too_slow,)),
    )
except ValueError:
    # Profile already registered elsewhere.
    pass


def _load_baseline() -> tuple[dict, dict]:
    thresholds = json.loads(scorecards.THRESHOLD_PATH.read_text(encoding="utf-8"))
    metrics = json.loads(scorecards.METRICS_PATH.read_text(encoding="utf-8"))
    return thresholds, metrics


def _write_json(path: Path, payload: dict) -> None:
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def _make_threshold(
    *,
    metric_id: str,
    comparison: str,
    target: Decimal,
    unit: str,
) -> scorecards.Threshold:
    return scorecards.Threshold(
        metric_id=metric_id,
        display_name=f"metric::{metric_id}",
        comparison=comparison,
        target=target,
        unit=unit,
        description="desc",
        on_fail="runbook",
    )


def _make_measurement(*, metric_id: str, observed: Decimal, unit: str) -> scorecards.Measurement:
    return scorecards.Measurement(
        metric_id=metric_id,
        observed=observed,
        unit=unit,
        sample_size=42,
        window="rolling",
    )


def test_generate_report_produces_pass_bundle(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    thresholds, metrics = _load_baseline()
    threshold_path = tmp_path / "thresholds.json"
    metrics_path = tmp_path / "metrics.json"
    _write_json(threshold_path, thresholds)
    _write_json(metrics_path, metrics)
    output_dir = tmp_path / "artifacts"
    monkeypatch.setattr(scorecards, "OUTPUT_DIR", output_dir)

    report = scorecards.generate_report(threshold_path, metrics_path)

    assert report["status"] == "PASS"
    guard_status = (output_dir / "guard_status.txt").read_text(encoding="utf-8")
    assert guard_status == "PASS\n"
    saved_report = json.loads((output_dir / "report.json").read_text(encoding="utf-8"))
    assert saved_report["bundle"]["sha256"] == report["bundle"]["sha256"]


def test_generate_report_handles_failures(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    thresholds, metrics = _load_baseline()
    metrics["metrics"]["divergence_pct"]["observed"] = 99.0
    threshold_path = tmp_path / "thresholds.json"
    metrics_path = tmp_path / "metrics.json"
    _write_json(threshold_path, thresholds)
    _write_json(metrics_path, metrics)
    output_dir = tmp_path / "artifacts"
    monkeypatch.setattr(scorecards, "OUTPUT_DIR", output_dir)

    report = scorecards.generate_report(threshold_path, metrics_path)

    assert report["status"] == "FAIL"
    guard_status = (output_dir / "guard_status.txt").read_text(encoding="utf-8")
    assert guard_status == "FAIL\n"


def test_generate_report_is_idempotent(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    thresholds, metrics = _load_baseline()
    threshold_path = tmp_path / "thresholds.json"
    metrics_path = tmp_path / "metrics.json"
    _write_json(threshold_path, thresholds)
    _write_json(metrics_path, metrics)
    output_dir = tmp_path / "artifacts"
    monkeypatch.setattr(scorecards, "OUTPUT_DIR", output_dir)

    class FrozenDateTime:
        @classmethod
        def now(cls, tz: dt.tzinfo | None = None) -> dt.datetime:
            tzinfo = tz or dt.timezone.utc
            return dt.datetime(2024, 1, 1, 12, 0, 0, tzinfo=tzinfo)

    monkeypatch.setattr(scorecards, "datetime", FrozenDateTime)

    scorecards.generate_report(threshold_path, metrics_path)
    first_snapshot = {
        item.name: item.read_text(encoding="utf-8") for item in sorted(output_dir.iterdir())
    }

    scorecards.generate_report(threshold_path, metrics_path)
    second_snapshot = {
        item.name: item.read_text(encoding="utf-8") for item in sorted(output_dir.iterdir())
    }

    assert first_snapshot == second_snapshot


def test_compare_respects_epsilon_bounds() -> None:
    target = Decimal("1.0")
    threshold_gte = _make_threshold(metric_id="quorum_ratio", comparison="gte", target=target, unit="ratio")
    close_pass = target - (scorecards.EPSILON / Decimal("2"))
    close_fail = target - (scorecards.EPSILON * 2)
    measurement_pass = _make_measurement(metric_id="quorum_ratio", observed=close_pass, unit="ratio")
    measurement_fail = _make_measurement(metric_id="quorum_ratio", observed=close_fail, unit="ratio")

    assert scorecards.compare(threshold_gte, measurement_pass).ok
    assert not scorecards.compare(threshold_gte, measurement_fail).ok

    threshold_lte = _make_threshold(metric_id="staleness_p95_s", comparison="lte", target=target, unit="seconds")
    lte_pass = target + (scorecards.EPSILON / Decimal("2"))
    lte_fail = target + (scorecards.EPSILON * 2)
    measurement_lte_pass = _make_measurement(
        metric_id="staleness_p95_s", observed=lte_pass, unit="seconds"
    )
    measurement_lte_fail = _make_measurement(
        metric_id="staleness_p95_s", observed=lte_fail, unit="seconds"
    )

    assert scorecards.compare(threshold_lte, measurement_lte_pass).ok
    assert not scorecards.compare(threshold_lte, measurement_lte_fail).ok


def test_canonical_dump_is_stable() -> None:
    payload = {"b": 1, "a": 2}
    dumped = scorecards.canonical_dump(payload)
    assert dumped.endswith("\n")
    expected = json.dumps(payload, sort_keys=True, ensure_ascii=False, separators=(",", ":")) + "\n"
    assert dumped == expected


@given(
    base=st.integers(min_value=1, max_value=5000),
    wiggle=st.integers(min_value=0, max_value=2000),
    relax=st.integers(min_value=0, max_value=2000),
)
@hp_settings(profile="ci")
@seed(12345)
def test_relaxing_gte_threshold_preserves_pass(base: int, wiggle: int, relax: int) -> None:
    target = Decimal(base) / Decimal("1000")
    measurement_value = target + Decimal(wiggle) / Decimal("1000")
    threshold = _make_threshold(metric_id="quorum_ratio", comparison="gte", target=target, unit="ratio")
    measurement = _make_measurement(metric_id="quorum_ratio", observed=measurement_value, unit="ratio")
    assert scorecards.compare(threshold, measurement).ok
    relaxed_target = target - Decimal(relax) / Decimal("1000")
    if relaxed_target < Decimal("0"):
        relaxed_target = Decimal("0")
    relaxed = replace(threshold, target=relaxed_target)
    assert scorecards.compare(relaxed, measurement).ok


@given(
    base=st.integers(min_value=1, max_value=5000),
    deficit=st.integers(min_value=1, max_value=2000),
    tighten=st.integers(min_value=0, max_value=2000),
)
@hp_settings(profile="ci")
@seed(12345)
def test_tightening_gte_threshold_preserves_failure(base: int, deficit: int, tighten: int) -> None:
    target = Decimal(base) / Decimal("1000")
    measurement_value = target - Decimal(deficit) / Decimal("1000")
    threshold = _make_threshold(metric_id="quorum_ratio", comparison="gte", target=target, unit="ratio")
    measurement = _make_measurement(metric_id="quorum_ratio", observed=measurement_value, unit="ratio")
    assert not scorecards.compare(threshold, measurement).ok
    tightened_target = target + Decimal(tighten) / Decimal("1000")
    tightened = replace(threshold, target=tightened_target)
    assert not scorecards.compare(tightened, measurement).ok


@given(
    base=st.integers(min_value=1, max_value=5000),
    wiggle=st.integers(min_value=0, max_value=2000),
    relax=st.integers(min_value=0, max_value=2000),
)
@hp_settings(profile="ci")
@seed(12345)
def test_relaxing_lte_threshold_preserves_pass(base: int, wiggle: int, relax: int) -> None:
    target = Decimal(base) / Decimal("1000")
    measurement_value = target - Decimal(wiggle) / Decimal("1000")
    threshold = _make_threshold(metric_id="staleness_p95_s", comparison="lte", target=target, unit="seconds")
    measurement = _make_measurement(
        metric_id="staleness_p95_s", observed=measurement_value, unit="seconds"
    )
    assert scorecards.compare(threshold, measurement).ok
    relaxed_target = target + Decimal(relax) / Decimal("1000")
    relaxed = replace(threshold, target=relaxed_target)
    assert scorecards.compare(relaxed, measurement).ok


@given(
    base=st.integers(min_value=1, max_value=5000),
    excess=st.integers(min_value=1, max_value=2000),
    tighten=st.integers(min_value=0, max_value=2000),
)
@hp_settings(profile="ci")
@seed(12345)
def test_tightening_lte_threshold_preserves_failure(base: int, excess: int, tighten: int) -> None:
    target = Decimal(base) / Decimal("1000")
    measurement_value = target + Decimal(excess) / Decimal("1000")
    threshold = _make_threshold(metric_id="staleness_p95_s", comparison="lte", target=target, unit="seconds")
    measurement = _make_measurement(
        metric_id="staleness_p95_s", observed=measurement_value, unit="seconds"
    )
    assert not scorecards.compare(threshold, measurement).ok
    tightened_target = target - Decimal(tighten) / Decimal("1000")
    if tightened_target < Decimal("0"):
        tightened_target = Decimal("0")
    tightened = replace(threshold, target=tightened_target)
    assert not scorecards.compare(tightened, measurement).ok


def test_contract_failure_missing_inputs(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    metrics_path = tmp_path / "metrics.json"
    metrics_path.write_text("{}", encoding="utf-8")
    output_dir = tmp_path / "artifacts"
    monkeypatch.setattr(scorecards, "OUTPUT_DIR", output_dir)

    with pytest.raises(RuntimeError) as excinfo:
        scorecards.generate_report(tmp_path / "missing.json", metrics_path)
    assert "S6-E-MISSING" in str(excinfo.value)
    guard_status = (output_dir / "guard_status.txt").read_text(encoding="utf-8")
    assert guard_status == "FAIL\n"


def test_contract_failure_schema_violation(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    thresholds = {"version": 1, "timestamp_utc": "2024-01-01T00:00:00Z"}
    metrics = {"version": 1, "timestamp_utc": "2024-01-01T00:00:00Z", "metrics": {}}
    threshold_path = tmp_path / "thresholds.json"
    metrics_path = tmp_path / "metrics.json"
    _write_json(threshold_path, thresholds)
    _write_json(metrics_path, metrics)
    output_dir = tmp_path / "artifacts"
    monkeypatch.setattr(scorecards, "OUTPUT_DIR", output_dir)

    with pytest.raises(RuntimeError) as excinfo:
        scorecards.generate_report(threshold_path, metrics_path)
    assert "S6-E-SCHEMA" in str(excinfo.value)
    guard_status = (output_dir / "guard_status.txt").read_text(encoding="utf-8")
    assert guard_status == "FAIL\n"


def test_contract_failure_encoding_error(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    threshold_path = tmp_path / "thresholds.json"
    threshold_path.write_bytes(b"\xff\xfe")
    metrics_path = tmp_path / "metrics.json"
    metrics_path.write_text("{}", encoding="utf-8")
    output_dir = tmp_path / "artifacts"
    monkeypatch.setattr(scorecards, "OUTPUT_DIR", output_dir)

    with pytest.raises(RuntimeError) as excinfo:
        scorecards.generate_report(threshold_path, metrics_path)
    assert "S6-E-ENCODING" in str(excinfo.value)
    guard_status = (output_dir / "guard_status.txt").read_text(encoding="utf-8")
    assert guard_status == "FAIL\n"
