from __future__ import annotations

import hashlib
import json
from pathlib import Path

import pytest

from scripts.boss_final import aggregate_q1

STAGES = aggregate_q1.STAGES
VARIANTS = ("primary", "clean")


def _freeze_time(monkeypatch: pytest.MonkeyPatch, timestamp: str = "2024-01-02T10:00:00Z") -> None:
    monkeypatch.setattr(aggregate_q1, "isoformat_utc", lambda: timestamp)


def _prepare_environment(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> Path:
    stages_dir = tmp_path / "stages"
    stages_dir.mkdir(parents=True)
    output_dir = tmp_path / "out"
    output_dir.mkdir(parents=True)
    monkeypatch.setattr(aggregate_q1, "STAGES_DIR", stages_dir)
    monkeypatch.setattr(aggregate_q1, "OUTPUT_DIR", output_dir)
    _freeze_time(monkeypatch)
    return stages_dir


def _write_variant(
    stages_dir: Path,
    stage: str,
    variant: str,
    *,
    status: str,
    notes: str,
    timestamp: str = "2024-01-02T09:00:00Z",
) -> None:
    variant_dir = stages_dir / stage / variant
    variant_dir.mkdir(parents=True, exist_ok=True)
    payload = {
        "stage": stage,
        "variant": variant,
        "status": status,
        "notes": notes,
        "timestamp_utc": timestamp,
        "checks": [],
    }
    (variant_dir / "result.json").write_text(json.dumps(payload, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    (variant_dir / "guard_status.txt").write_text(f"{status}\n", encoding="utf-8")
    (variant_dir / "bundle.sha256").write_text("deadbeef" * 8 + "\n", encoding="utf-8")


def _write_stage_summary(
    stages_dir: Path,
    stage: str,
    *,
    variant_status: dict[str, tuple[str, str]],
    timestamp: str = "2024-01-02T09:05:00Z",
    notes: str | None = None,
) -> None:
    stage_dir = stages_dir / stage
    stage_dir.mkdir(parents=True, exist_ok=True)
    variants_payload: dict[str, dict[str, str]] = {}
    for variant, (status, note) in variant_status.items():
        variants_payload[variant] = {"status": status, "notes": note}
    stage_status = "PASS" if all(status == "PASS" for status, _ in variant_status.values()) else "FAIL"
    summary_notes = notes if notes is not None else " | ".join(
        f"{variant}:{status}{(' ' + note) if note else ''}"
        for variant, (status, note) in variant_status.items()
    )
    payload = {
        "stage": stage,
        "status": stage_status,
        "notes": summary_notes.strip(),
        "variants": variants_payload,
        "timestamp_utc": timestamp,
    }
    (stage_dir / "summary.json").write_text(json.dumps(payload, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    (stage_dir / "guard_status.txt").write_text(f"{stage_status}\n", encoding="utf-8")


def _prime_stage(
    stages_dir: Path,
    stage: str,
    *,
    primary_status: str = "PASS",
    clean_status: str = "PASS",
    primary_notes: str = "ok",
    clean_notes: str = "ok",
) -> None:
    _write_variant(stages_dir, stage, "primary", status=primary_status, notes=primary_notes)
    _write_variant(stages_dir, stage, "clean", status=clean_status, notes=clean_notes)
    _write_stage_summary(
        stages_dir,
        stage,
        variant_status={
            "primary": (primary_status, primary_notes),
            "clean": (clean_status, clean_notes),
        },
    )


def _load_json(path: Path) -> dict[str, object]:
    return json.loads(path.read_text(encoding="utf-8"))


def _manual_global_bundle(stages_dir: Path) -> str:
    pieces: list[str] = []
    for stage in STAGES:
        stage_dir = stages_dir / stage
        summary = _load_json(stage_dir / "summary.json")
        pieces.append(json.dumps(summary, sort_keys=True, ensure_ascii=False, separators=(",", ":")) + "\n")
        for variant in VARIANTS:
            result = _load_json(stage_dir / variant / "result.json")
            payload = {
                "stage": summary["stage"],
                "variant": variant,
                "status": result["status"],
                "notes": result["notes"],
                "timestamp_utc": result["timestamp_utc"],
            }
            pieces.append(json.dumps(payload, sort_keys=True, ensure_ascii=False, separators=(",", ":")) + "\n")
    return hashlib.sha256("".join(pieces).encode("utf-8")).hexdigest()


def test_aggregate_success(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    stages_dir = _prepare_environment(tmp_path, monkeypatch)
    for stage in STAGES:
        _prime_stage(stages_dir, stage, primary_notes=f"{stage}-primary", clean_notes=f"{stage}-clean")

    artifacts = aggregate_q1.aggregate()

    report = _load_json(aggregate_q1.OUTPUT_DIR / "report.json")
    assert report["status"] == "PASS"
    assert report["schema_version"] == aggregate_q1.SCHEMA_VERSION
    for stage in STAGES:
        assert report["sprints"][stage]["status"] == "PASS"
        assert report["sprints"][stage]["notes"].startswith("primary:PASS")
    assert _manual_global_bundle(aggregate_q1.STAGES_DIR) == artifacts.bundle_sha256
    badge = (aggregate_q1.OUTPUT_DIR / "badge.svg").read_text(encoding="utf-8")
    assert "Q1 Boss" in badge and "PASS" in badge
    dag = (aggregate_q1.OUTPUT_DIR / "dag.svg").read_text(encoding="utf-8")
    assert all(stage.upper() in dag for stage in STAGES)
    guard = (aggregate_q1.OUTPUT_DIR / "guard_status.txt").read_text(encoding="utf-8").strip()
    assert guard == "PASS"


def test_stage_failure_propagates(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    stages_dir = _prepare_environment(tmp_path, monkeypatch)
    for stage in STAGES:
        if stage == "s3":
            _prime_stage(stages_dir, stage, primary_status="FAIL", clean_status="PASS", primary_notes="failed", clean_notes="ok")
        else:
            _prime_stage(stages_dir, stage)

    with pytest.raises(SystemExit):
        aggregate_q1.aggregate()

    report = _load_json(aggregate_q1.OUTPUT_DIR / "report.json")
    assert report["status"] == "FAIL"
    assert report["sprints"]["s3"]["status"] == "FAIL"
    guard = (aggregate_q1.OUTPUT_DIR / "guard_status.txt").read_text(encoding="utf-8").strip()
    assert guard == "FAIL"


def test_missing_summary_fails(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    stages_dir = _prepare_environment(tmp_path, monkeypatch)
    for stage in STAGES:
        _prime_stage(stages_dir, stage)
    (stages_dir / "s4" / "summary.json").unlink()

    with pytest.raises(RuntimeError) as excinfo:
        aggregate_q1.aggregate()
    assert "E-SUMMARY" in str(excinfo.value)


def test_guard_mismatch_detected(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    stages_dir = _prepare_environment(tmp_path, monkeypatch)
    for stage in STAGES:
        _prime_stage(stages_dir, stage)
    (stages_dir / "s2" / "guard_status.txt").write_text("FAIL\n", encoding="utf-8")

    with pytest.raises(RuntimeError) as excinfo:
        aggregate_q1.aggregate()
    assert "E-SUMMARY-MISMATCH" in str(excinfo.value)


def test_variant_guard_mismatch_detected(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    stages_dir = _prepare_environment(tmp_path, monkeypatch)
    for stage in STAGES:
        _prime_stage(stages_dir, stage)
    (stages_dir / "s5" / "primary" / "guard_status.txt").write_text("FAIL\n", encoding="utf-8")

    with pytest.raises(RuntimeError) as excinfo:
        aggregate_q1.aggregate()
    assert "E-GUARD-MISMATCH" in str(excinfo.value)


def test_pr_comment_contains_notes(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    stages_dir = _prepare_environment(tmp_path, monkeypatch)
    for stage in STAGES:
        _prime_stage(stages_dir, stage, primary_notes="ready", clean_notes="steady")

    artifacts = aggregate_q1.aggregate()
    comment = (aggregate_q1.OUTPUT_DIR / "pr_comment.md").read_text(encoding="utf-8")
    assert artifacts.report["status"] in comment
    for stage in STAGES:
        assert stage.upper() in comment


def test_aggregate_with_release_tag(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    stages_dir = _prepare_environment(tmp_path, monkeypatch)
    for stage in STAGES:
        _prime_stage(stages_dir, stage)

    artifacts = aggregate_q1.aggregate("v1.2.3")
    report = _load_json(aggregate_q1.OUTPUT_DIR / "report.json")
    assert report["release_tag"] == "v1.2.3"
    assert artifacts.report["status"] == "PASS"
