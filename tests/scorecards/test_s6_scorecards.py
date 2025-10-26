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
    METRIC_DEFINITIONS,
    ScorecardArtifacts,
    ScorecardError,
    compare,
    evaluate_metrics,
    format_value,
)


DECIMAL_VALUES = st.decimals(
    min_value=-50,
    max_value=50,
    places=4,
    allow_nan=False,
    allow_infinity=False,
)


def _freeze_datetime(monkeypatch: pytest.MonkeyPatch) -> None:
    class FrozenDateTime(datetime):
        @classmethod
        def now(cls, tz: timezone | None = None) -> datetime:
            return datetime(2024, 1, 1, 12, 0, 0, tzinfo=tz or timezone.utc)

    monkeypatch.setattr(scorecards, "datetime", FrozenDateTime)


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
    thresholds_path.write_text(json.dumps({"version": 1}), encoding="utf-8")

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
