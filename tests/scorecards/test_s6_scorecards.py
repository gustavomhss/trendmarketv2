from __future__ import annotations

import json
from datetime import datetime, timezone
from decimal import Decimal
from pathlib import Path

import pytest
from hypothesis import given, strategies as st

from scripts.scorecards import s6_scorecards as scorecards
from scripts.scorecards.s6_scorecards import (
    EPSILON,
    Measurement,
    ScorecardError,
    Threshold,
)


DECIMAL_VALUES = st.decimals(
    min_value=-50,
    max_value=50,
    places=4,
    allow_nan=False,
    allow_infinity=False,
)
POSITIVE_DECIMALS = st.decimals(
    min_value=0,
    max_value=10,
    places=4,
    allow_nan=False,
    allow_infinity=False,
)


def make_threshold(metric_id: str, comparison: str, target: Decimal, order: int = 1) -> Threshold:
    return Threshold(
        metric_id=metric_id,
        order=order,
        display_name=f"Metric {metric_id.upper()}",
        comparison=comparison,
        target_value=target,
        unit="percent",
        description="desc",
        on_fail="fix",
    )


def make_measurement(metric_id: str, value: Decimal) -> Measurement:
    return Measurement(
        metric_id=metric_id,
        value=value,
        unit="percent",
        sample_size=100,
        measurement="2024-01-01/2024-01-02",
    )


@given(target=st.integers(-10, 10))
def test_compare_gte_respects_epsilon_boundary(target: int) -> None:
    target_decimal = Decimal(target)
    threshold = make_threshold("m1", "gte", target_decimal)
    within_epsilon = make_measurement("m1", target_decimal - (EPSILON / 2))
    status, delta = scorecards.compare(threshold, within_epsilon)
    assert status == "pass"
    assert delta == within_epsilon.value - target_decimal

    beyond_epsilon = make_measurement("m1", target_decimal - (EPSILON * 2))
    status, _ = scorecards.compare(threshold, beyond_epsilon)
    assert status == "fail"


@given(target=st.integers(-10, 10))
def test_compare_lte_respects_epsilon_boundary(target: int) -> None:
    target_decimal = Decimal(target)
    threshold = make_threshold("m2", "lte", target_decimal)
    within_epsilon = make_measurement("m2", target_decimal + (EPSILON / 2))
    status, delta = scorecards.compare(threshold, within_epsilon)
    assert status == "pass"
    assert delta == target_decimal - within_epsilon.value

    beyond_epsilon = make_measurement("m2", target_decimal + (EPSILON * 2))
    status, _ = scorecards.compare(threshold, beyond_epsilon)
    assert status == "fail"


@given(
    target=DECIMAL_VALUES,
    measurement_delta=DECIMAL_VALUES,
    relax=POSITIVE_DECIMALS,
    tighten=POSITIVE_DECIMALS,
)
def test_metamorphic_relax_and_tighten_gte(
    target: Decimal,
    measurement_delta: Decimal,
    relax: Decimal,
    tighten: Decimal,
) -> None:
    threshold = make_threshold("m3", "gte", target)
    measurement_value = target - measurement_delta
    measurement = make_measurement("m3", measurement_value)
    status, _ = scorecards.compare(threshold, measurement)

    relaxed_threshold = make_threshold("m3", "gte", target - relax)
    relaxed_status, _ = scorecards.compare(relaxed_threshold, measurement)
    if status == "pass":
        assert relaxed_status == "pass"

    tightened_threshold = make_threshold("m3", "gte", target + tighten)
    tightened_status, _ = scorecards.compare(tightened_threshold, measurement)
    if status == "fail":
        assert tightened_status == "fail"


@given(
    target=DECIMAL_VALUES,
    measurement_delta=DECIMAL_VALUES,
    relax=POSITIVE_DECIMALS,
    tighten=POSITIVE_DECIMALS,
)
def test_metamorphic_relax_and_tighten_lte(
    target: Decimal,
    measurement_delta: Decimal,
    relax: Decimal,
    tighten: Decimal,
) -> None:
    threshold = make_threshold("m4", "lte", target)
    measurement_value = target + measurement_delta
    measurement = make_measurement("m4", measurement_value)
    status, _ = scorecards.compare(threshold, measurement)

    relaxed_threshold = make_threshold("m4", "lte", target + relax)
    relaxed_status, _ = scorecards.compare(relaxed_threshold, measurement)
    if status == "pass":
        assert relaxed_status == "pass"

    tightened_threshold = make_threshold("m4", "lte", target - tighten)
    tightened_status, _ = scorecards.compare(tightened_threshold, measurement)
    if status == "fail":
        assert tightened_status == "fail"


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
    assert scorecards.format_value(value, unit) == expected


def _write_inputs(tmp_path: Path) -> tuple[Path, Path]:
    thresholds = {
        "schema_version": 1,
        "generated_at": "2024-01-01T00:00:00Z",
        "metrics": [
            {
                "id": "metric_availability",
                "order": 1,
                "display_name": "Availability",
                "comparison": "gte",
                "target_value": "99.95",
                "unit": "percent",
                "description": "Availability target",
                "on_fail": "Scale the service",
            }
        ],
    }
    metrics = {
        "schema_version": 1,
        "collected_at": "2024-01-01T00:00:00Z",
        "metrics": [
            {
                "id": "metric_availability",
                "value": "99.97",
                "unit": "percent",
                "sample_size": 4800,
                "measurement": "2024-01-01/2024-01-02",
            }
        ],
    }
    thresholds_path = tmp_path / "thresholds.json"
    metrics_path = tmp_path / "metrics.json"
    thresholds_path.write_text(json.dumps(thresholds), encoding="utf-8")
    metrics_path.write_text(json.dumps(metrics), encoding="utf-8")
    return thresholds_path, metrics_path


def _freeze_datetime(monkeypatch: pytest.MonkeyPatch) -> None:
    class FrozenDateTime(datetime):
        @classmethod
        def now(cls, tz: timezone | None = None) -> datetime:
            return datetime(2024, 1, 1, 12, 0, 0, tzinfo=tz or timezone.utc)

    monkeypatch.setattr(scorecards, "datetime", FrozenDateTime)


def test_generate_report_is_idempotent(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    output_dir = tmp_path / "out"
    monkeypatch.setattr(scorecards, "OUTPUT_DIR", output_dir)
    _freeze_datetime(monkeypatch)
    thresholds_path, metrics_path = _write_inputs(tmp_path)

    report_first = scorecards.generate_report(thresholds_path, metrics_path)
    markdown_first = (output_dir / "report.md").read_text(encoding="utf-8")
    bundle_hash_first = report_first["bundle_sha256"]

    report_second = scorecards.generate_report(thresholds_path, metrics_path)
    markdown_second = (output_dir / "report.md").read_text(encoding="utf-8")

    assert report_second["bundle_sha256"] == bundle_hash_first
    assert markdown_first == markdown_second
    assert (output_dir / "bundle.sha256").read_text(encoding="utf-8").strip() == bundle_hash_first
    assert (output_dir / "guard_status.txt").read_text(encoding="utf-8").strip() == "PASS"
    assert "| Métrica | Valor |" in markdown_first


def test_generate_report_missing_thresholds(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    output_dir = tmp_path / "out"
    monkeypatch.setattr(scorecards, "OUTPUT_DIR", output_dir)
    _, metrics_path = _write_inputs(tmp_path)

    with pytest.raises(ScorecardError) as exc:
        scorecards.generate_report(tmp_path / "missing.json", metrics_path)
    assert exc.value.code == "S6-E-MISSING"


def test_generate_report_schema_violation(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    output_dir = tmp_path / "out"
    monkeypatch.setattr(scorecards, "OUTPUT_DIR", output_dir)
    thresholds_path, metrics_path = _write_inputs(tmp_path)
    thresholds_path.write_text(
        json.dumps({"schema_version": 1, "generated_at": "2024-01-01T00:00:00Z"}),
        encoding="utf-8",
    )

    with pytest.raises(ScorecardError) as exc:
        scorecards.generate_report(thresholds_path, metrics_path)
    assert exc.value.code == "S6-E-SCHEMA"


def test_generate_report_invalid_encoding(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    output_dir = tmp_path / "out"
    monkeypatch.setattr(scorecards, "OUTPUT_DIR", output_dir)
    thresholds_path, metrics_path = _write_inputs(tmp_path)
    thresholds_path.write_bytes(b"\xff\xfe\x00invalid")

    with pytest.raises(ScorecardError) as exc:
        scorecards.generate_report(thresholds_path, metrics_path)
    assert exc.value.code == "S6-E-ENCODING"
