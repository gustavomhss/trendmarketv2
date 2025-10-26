from __future__ import annotations

import json
from datetime import datetime, timezone
from decimal import Decimal
from pathlib import Path

import pytest
from hypothesis import HealthCheck, given, seed, settings
from hypothesis import strategies as st

from scripts.scorecards import s6_scorecards as scorecards


try:  # pragma: no branch - test environments may register the profile already
    settings.register_profile(
        "ci",
        settings(
            max_examples=50,
            deadline=None,
            suppress_health_check=(HealthCheck.too_slow,),
        ),
    )
except ValueError:
    pass


def _freeze_now(monkeypatch: pytest.MonkeyPatch, when: datetime) -> None:
    class FrozenDateTime(datetime):
        @classmethod
        def now(cls, tz: timezone | None = None) -> datetime:
            return when.astimezone(tz or timezone.utc)

    monkeypatch.setattr(scorecards, "datetime", FrozenDateTime)


def _write_inputs(tmp_path: Path, *, pass_fail: tuple[bool, bool] = (True, True)) -> tuple[Path, Path]:
    thresholds = {
        "version": 4,
        "timestamp_utc": "2024-01-01T00:00:00Z",
        "quorum_ratio_min": 0.985,
        "failover_time_p95_s_max": 3.1,
        "staleness_p95_s_max": 2.0,
        "cdc_lag_p95_s_max": 1.7,
        "divergence_pct_max": 0.5,
    }
    metrics = {
        "version": 9,
        "timestamp_utc": "2024-01-02T00:00:00Z",
        "quorum_ratio": 0.99 if pass_fail[0] else 0.90,
        "failover_time_p95_s": 2.0 if pass_fail[1] else 3.5,
        "staleness_p95_s": 1.5,
        "cdc_lag_p95_s": 1.0,
        "divergence_pct": 0.2,
    }

    thresholds_path = tmp_path / "thresholds.json"
    metrics_path = tmp_path / "metrics.json"
    thresholds_path.write_text(json.dumps(thresholds), encoding="utf-8")
    metrics_path.write_text(json.dumps(metrics), encoding="utf-8")
    return thresholds_path, metrics_path


@given(st.decimals(min_value=0, max_value=1, places=6))
@settings(profile="ci")
@seed(12345)
def test_compare_respects_epsilon_for_gte(observed: Decimal) -> None:
    assert scorecards._compare(  # type: ignore[attr-defined]
        observed - (scorecards.EPSILON / 2), observed, "gte"
    )


@given(st.decimals(min_value=0, max_value=10, places=6))
@settings(profile="ci")
@seed(54321)
def test_compare_respects_epsilon_for_lte(value: Decimal) -> None:
    assert scorecards._compare(  # type: ignore[attr-defined]
        value + (scorecards.EPSILON / 2), value, "lte"
    )


def test_evaluate_metrics_pass_fail_matrix(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    output_dir = tmp_path / "out"
    monkeypatch.setattr(scorecards, "OUTPUT_DIR", output_dir)
    _freeze_now(monkeypatch, datetime(2024, 1, 1, 12, tzinfo=timezone.utc))

    thresholds_path, metrics_path = _write_inputs(tmp_path, pass_fail=(True, False))
    artifacts = scorecards.generate_report(thresholds_path, metrics_path)

    assert artifacts.report["status"] == "FAIL"
    failing = [metric for metric in artifacts.results if not metric.ok]
    assert {metric.spec.key for metric in failing} == {"failover_time_p95_s"}
    markdown = (output_dir / "report.md").read_text(encoding="utf-8")
    assert "❌ FAIL" in markdown
    assert (output_dir / "guard_status.txt").read_text(encoding="utf-8") == "FAIL\n"
    pr_comment = (output_dir / "pr_comment.md").read_text(encoding="utf-8")
    assert "- Failover Time p95 (s):" in pr_comment


@given(
    base=st.decimals(min_value=0, max_value=10, places=4),
    delta=st.decimals(min_value=0, max_value=5, places=4),
    relax=st.decimals(min_value=0, max_value=1, places=4),
    tighten=st.decimals(min_value=0, max_value=1, places=4),
)
@settings(profile="ci")
@seed(4242)
def test_metamorphic_threshold_adjustments(
    base: Decimal, delta: Decimal, relax: Decimal, tighten: Decimal
) -> None:
    observed_gte = base - delta
    target = base
    status = scorecards._compare(observed_gte, target, "gte")  # type: ignore[attr-defined]
    relaxed_status = scorecards._compare(
        observed_gte, target - relax, "gte"
    )  # type: ignore[attr-defined]
    tightened_status = scorecards._compare(
        observed_gte, target + tighten, "gte"
    )  # type: ignore[attr-defined]

    if status:
        assert relaxed_status is True
    else:
        assert tightened_status is False


def test_markdown_contains_table(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    output_dir = tmp_path / "scorecards"
    monkeypatch.setattr(scorecards, "OUTPUT_DIR", output_dir)
    _freeze_now(monkeypatch, datetime(2024, 3, 2, 18, tzinfo=timezone.utc))

    paths = _write_inputs(tmp_path)
    artifacts = scorecards.generate_report(*paths)
    markdown = (output_dir / "report.md").read_text(encoding="utf-8")

    assert "| Métrica | Observado | Alvo | Status |" in markdown
    assert artifacts.bundle_sha256 == (output_dir / "bundle.sha256").read_text(encoding="utf-8").strip()
    pr_comment = (output_dir / "pr_comment.md").read_text(encoding="utf-8")
    assert "![Status](./badge.svg)" in pr_comment


@pytest.mark.parametrize(
    "value, suffix, expected",
    [
        (Decimal("1.2345"), "", "1.2345"),
        (Decimal("2.0000"), "s", "2s"),
        (Decimal("0.100"), "%", "0.1%"),
    ],
)
def test_format_decimal(value: Decimal, suffix: str, expected: str) -> None:
    assert scorecards._format_decimal(value, suffix) == expected  # type: ignore[attr-defined]


def test_idempotent_reruns(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    output_dir = tmp_path / "rerun"
    monkeypatch.setattr(scorecards, "OUTPUT_DIR", output_dir)
    _freeze_now(monkeypatch, datetime(2024, 4, 1, 15, tzinfo=timezone.utc))
    paths = _write_inputs(tmp_path)

    first = scorecards.generate_report(*paths)
    first_markdown = (output_dir / "report.md").read_text(encoding="utf-8")
    second = scorecards.generate_report(*paths)
    second_markdown = (output_dir / "report.md").read_text(encoding="utf-8")

    assert first.bundle_sha256 == second.bundle_sha256
    assert first_markdown == second_markdown
    assert (output_dir / "guard_status.txt").read_text(encoding="utf-8") == "PASS\n"


def test_failure_missing_inputs(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    output_dir = tmp_path / "missing"
    monkeypatch.setattr(scorecards, "OUTPUT_DIR", output_dir)
    metrics_path = tmp_path / "metrics.json"
    metrics_path.write_text(
        json.dumps(
            {
                "version": 1,
                "timestamp_utc": "2024-01-01T00:00:00Z",
                "quorum_ratio": 0.9,
                "failover_time_p95_s": 1.0,
                "staleness_p95_s": 1.0,
                "cdc_lag_p95_s": 1.0,
                "divergence_pct": 0.1,
            }
        ),
        encoding="utf-8",
    )

    with pytest.raises(scorecards.ScorecardError) as exc:
        scorecards.generate_report(tmp_path / "thresholds.json", metrics_path)
    assert exc.value.code == "S6-E-MISSING"


def test_failure_schema_violation(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    output_dir = tmp_path / "schema"
    monkeypatch.setattr(scorecards, "OUTPUT_DIR", output_dir)
    thresholds_path, metrics_path = _write_inputs(tmp_path)
    thresholds_path.write_text(json.dumps({"version": 1}), encoding="utf-8")

    with pytest.raises(scorecards.ScorecardError) as exc:
        scorecards.generate_report(thresholds_path, metrics_path)
    assert exc.value.code == "S6-E-SCHEMA"


def test_failure_encoding(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    output_dir = tmp_path / "encoding"
    monkeypatch.setattr(scorecards, "OUTPUT_DIR", output_dir)
    thresholds_path, metrics_path = _write_inputs(tmp_path)
    thresholds_path.write_bytes(b"\xff\xfe\x00invalid")

    with pytest.raises(scorecards.ScorecardError) as exc:
        scorecards.generate_report(thresholds_path, metrics_path)
    assert exc.value.code == "S6-E-ENCODING"

