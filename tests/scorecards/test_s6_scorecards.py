from __future__ import annotations

import hashlib
import json
from decimal import Decimal
from pathlib import Path

import pytest
from hypothesis import HealthCheck, Phase, given, settings
from hypothesis import strategies as st

from scripts.scorecards import s6_scorecards

FIXTURES_DIR = Path(__file__).resolve().parents[2] / "s6_validation"

settings.register_profile(
    "ci",
    settings(
        max_examples=50,
        suppress_health_check=(HealthCheck.too_slow,),
        phases=(Phase.explicit, Phase.reuse, Phase.generate),
    ),
)
settings.load_profile("ci")


def _write_json(path: Path, payload: dict[str, object]) -> None:
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _load_fixture(name: str) -> dict[str, object]:
    return json.loads((FIXTURES_DIR / name).read_text(encoding="utf-8"))


@pytest.fixture
def output_dir(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> Path:
    directory = tmp_path / "scorecards"
    monkeypatch.setattr(s6_scorecards, "OUTPUT_DIR", directory)
    return directory


@pytest.fixture
def inputs(tmp_path: Path) -> tuple[Path, Path]:
    thresholds = _load_fixture("thresholds.json")
    metrics = _load_fixture("metrics_static.json")
    thresholds_path = tmp_path / "thresholds.json"
    metrics_path = tmp_path / "metrics.json"
    _write_json(thresholds_path, thresholds)
    _write_json(metrics_path, metrics)
    return thresholds_path, metrics_path


def _freeze_time(
    monkeypatch: pytest.MonkeyPatch, timestamp: str = "2024-01-02T06:00:00Z"
) -> None:
    monkeypatch.setattr(s6_scorecards, "isoformat_utc", lambda: timestamp)


def test_generate_report_pass(
    output_dir: Path, inputs: tuple[Path, Path], monkeypatch: pytest.MonkeyPatch
) -> None:
    _freeze_time(monkeypatch)
    thresholds_path, metrics_path = inputs

    artifacts = s6_scorecards.generate_report(
        threshold_path=thresholds_path, metrics_path=metrics_path
    )

    guard_status = (output_dir / "guard_status.txt").read_text(encoding="utf-8").strip()
    assert guard_status == "PASS"
    report = json.loads((output_dir / "report.json").read_text(encoding="utf-8"))
    assert report["status"] == "PASS"
    assert report["bundle"]["sha256"] == artifacts.bundle_sha256


def test_generate_report_fail_sets_guard(
    output_dir: Path, inputs: tuple[Path, Path], monkeypatch: pytest.MonkeyPatch
) -> None:
    _freeze_time(monkeypatch)
    thresholds_path, metrics_path = inputs
    metrics_payload = json.loads(metrics_path.read_text(encoding="utf-8"))
    metrics_payload["failover_time_p95_s"]["observed"] = 120.0
    _write_json(metrics_path, metrics_payload)

    artifacts = s6_scorecards.generate_report(
        threshold_path=thresholds_path, metrics_path=metrics_path
    )

    guard_status = (output_dir / "guard_status.txt").read_text(encoding="utf-8").strip()
    assert guard_status == "FAIL"
    assert artifacts.report["status"] == "FAIL"


def test_bundle_hash_matches_manual(tmp_path: Path) -> None:
    thresholds = _load_fixture("thresholds.json")
    metrics = _load_fixture("metrics_static.json")
    thresholds_path = tmp_path / "thresholds.json"
    metrics_path = tmp_path / "metrics.json"
    _write_json(thresholds_path, thresholds)
    _write_json(metrics_path, metrics)

    artifacts = s6_scorecards.generate_report(
        threshold_path=thresholds_path, metrics_path=metrics_path
    )

    canonical = (
        s6_scorecards.canonical_dumps(thresholds)
        + "\n"
        + s6_scorecards.canonical_dumps(metrics)
        + "\n"
    ).encode("utf-8")
    expected = hashlib.sha256(canonical).hexdigest()
    assert artifacts.bundle_sha256 == expected


def test_idempotent_reruns(
    output_dir: Path, inputs: tuple[Path, Path], monkeypatch: pytest.MonkeyPatch
) -> None:
    _freeze_time(monkeypatch)
    thresholds_path, metrics_path = inputs
    first = s6_scorecards.generate_report(
        threshold_path=thresholds_path, metrics_path=metrics_path
    )
    snapshot_one = {
        path.name: path.read_text(encoding="utf-8")
        for path in sorted(output_dir.iterdir())
    }

    second = s6_scorecards.generate_report(
        threshold_path=thresholds_path, metrics_path=metrics_path
    )
    snapshot_two = {
        path.name: path.read_text(encoding="utf-8")
        for path in sorted(output_dir.iterdir())
    }

    assert first.bundle_sha256 == second.bundle_sha256
    assert snapshot_one == snapshot_two


def test_missing_metric_raises(tmp_path: Path) -> None:
    thresholds = _load_fixture("thresholds.json")
    metrics = _load_fixture("metrics_static.json")
    metrics.pop("divergence_pct")
    thresholds_path = tmp_path / "thresholds.json"
    metrics_path = tmp_path / "metrics.json"
    _write_json(thresholds_path, thresholds)
    _write_json(metrics_path, metrics)

    with pytest.raises(s6_scorecards.ScorecardError) as excinfo:
        s6_scorecards.generate_report(
            threshold_path=thresholds_path, metrics_path=metrics_path
        )
    assert excinfo.value.code == "S6-E-SCHEMA"


def test_load_json_invalid_schema(tmp_path: Path) -> None:
    payload = {
        "schema": "trendmarketv2.sprint6.metrics",
        "schema_version": 2,
        "timestamp_utc": "2024-09-02T06:00:00Z",
        "quorum_ratio": {
            "observed": -1.0,
            "unit": "ratio",
            "sample_size": 10,
            "window": "24h",
        },
        "failover_time_p95_s": {
            "observed": 1.0,
            "unit": "seconds",
            "sample_size": 10,
            "window": "24h",
        },
        "staleness_p95_s": {
            "observed": 1.0,
            "unit": "seconds",
            "sample_size": 10,
            "window": "24h",
        },
        "cdc_lag_p95_s": {
            "observed": 1.0,
            "unit": "seconds",
            "sample_size": 10,
            "window": "24h",
        },
        "divergence_pct": {
            "observed": 0.5,
            "unit": "percent",
            "sample_size": 10,
            "window": "24h",
        },
    }
    path = tmp_path / "metrics.json"
    _write_json(path, payload)

    with pytest.raises(s6_scorecards.ScorecardError) as excinfo:
        s6_scorecards.load_json(path, "metrics")
    assert excinfo.value.code == "S6-E-SCHEMA"


def test_compare_invalid_operator() -> None:
    with pytest.raises(s6_scorecards.ScorecardError) as excinfo:
        s6_scorecards.compare_values("neq", Decimal("1"), Decimal("1"))
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


@given(
    target=st.decimals(min_value=Decimal("0.7"), max_value=Decimal("0.99"), places=4)
)
def test_evaluate_respects_epsilon_gte(target: Decimal) -> None:
    thresholds = _load_fixture("thresholds.json")
    metrics = _load_fixture("metrics_static.json")
    thresholds["quorum_ratio"] = float(target)
    metrics["quorum_ratio"]["observed"] = float(target - (s6_scorecards.EPSILON / 2))

    results = s6_scorecards.evaluate_metrics(thresholds, metrics)
    quorum = next(item for item in results if item.definition.key == "quorum_ratio")
    assert quorum.ok

    metrics["quorum_ratio"]["observed"] = float(target - (s6_scorecards.EPSILON * 4))
    results = s6_scorecards.evaluate_metrics(thresholds, metrics)
    quorum = next(item for item in results if item.definition.key == "quorum_ratio")
    assert not quorum.ok


@given(target=st.decimals(min_value=Decimal("1"), max_value=Decimal("120"), places=3))
def test_evaluate_respects_epsilon_lte(target: Decimal) -> None:
    thresholds = _load_fixture("thresholds.json")
    metrics = _load_fixture("metrics_static.json")
    thresholds["failover_time_p95_s"] = float(target)
    metrics["failover_time_p95_s"]["observed"] = float(
        target + (s6_scorecards.EPSILON / 2)
    )

    results = s6_scorecards.evaluate_metrics(thresholds, metrics)
    failover = next(
        item for item in results if item.definition.key == "failover_time_p95_s"
    )
    assert failover.ok

    metrics["failover_time_p95_s"]["observed"] = float(
        target + (s6_scorecards.EPSILON * 4)
    )
    results = s6_scorecards.evaluate_metrics(thresholds, metrics)
    failover = next(
        item for item in results if item.definition.key == "failover_time_p95_s"
    )
    assert not failover.ok
