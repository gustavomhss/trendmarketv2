from __future__ import annotations

import hashlib
import json
from pathlib import Path

import pytest

from scripts.boss_final import aggregate_q1

STAGES = aggregate_q1.STAGES
VARIANTS = aggregate_q1.VARIANTS


def _freeze_time(
    monkeypatch: pytest.MonkeyPatch, timestamp: str = "2024-01-02T10:00:00Z"
) -> None:
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
    (variant_dir / "result.json").write_text(
        json.dumps(payload, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )
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
        variants_payload[variant] = {
            "status": status,
            "notes": note,
            "timestamp_utc": "2024-01-02T09:00:00Z",
        }
    stage_status = (
        "PASS"
        if all(status == "PASS" for status, _ in variant_status.values())
        else "FAIL"
    )
    summary_notes = (
        notes
        if notes is not None
        else " | ".join(
            f"{variant}:{status}{(' ' + note) if note else ''}"
            for variant, (status, note) in variant_status.items()
        )
    )
    payload = {
        "stage": stage,
        "status": stage_status,
        "notes": summary_notes.strip(),
        "variants": variants_payload,
        "timestamp_utc": timestamp,
    }
    (stage_dir / "summary.json").write_text(
        json.dumps(payload, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )
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
    _write_variant(
        stages_dir, stage, "primary", status=primary_status, notes=primary_notes
    )
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


def _manual_bundle(stages_dir: Path) -> str:
    pieces: list[str] = []
    for stage in STAGES:
        stage_dir = stages_dir / stage
        summary = _load_json(stage_dir / "summary.json")
        summary_payload = {
            "stage": stage,
            "status": summary["status"],
            "notes": summary["notes"],
        }
        pieces.append(aggregate_q1.canonical_dumps(summary_payload) + "\n")
        for variant in VARIANTS:
            result = _load_json(stage_dir / variant / "result.json")
            variant_payload = {
                "stage": stage,
                "variant": variant,
                "status": result["status"],
                "notes": result["notes"],
                "timestamp_utc": result["timestamp_utc"],
            }
            pieces.append(aggregate_q1.canonical_dumps(variant_payload) + "\n")
    return hashlib.sha256("".join(pieces).encode("utf-8")).hexdigest()


def test_aggregate_pass(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    stages_dir = _prepare_environment(tmp_path, monkeypatch)
    for stage in STAGES:
        _prime_stage(
            stages_dir, stage, primary_notes=f"{stage} ok", clean_notes=f"{stage} ok"
        )

    report = aggregate_q1.aggregate()

    assert report["status"] == "PASS"
    guard_status = (
        (aggregate_q1.OUTPUT_DIR / "guard_status.txt")
        .read_text(encoding="utf-8")
        .strip()
    )
    assert guard_status == "PASS"
    report_json = _load_json(aggregate_q1.OUTPUT_DIR / "report.json")
    assert report_json["bundle"]["sha256"] == report["bundle"]["sha256"]


def test_aggregate_detects_mismatch(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    stages_dir = _prepare_environment(tmp_path, monkeypatch)
    for stage in STAGES:
        _prime_stage(stages_dir, stage)
    # Break guard for s4
    (stages_dir / "s4" / "guard_status.txt").write_text("FAIL\n", encoding="utf-8")

    with pytest.raises(RuntimeError):
        aggregate_q1.aggregate()


def test_bundle_sha_manual_match(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    stages_dir = _prepare_environment(tmp_path, monkeypatch)
    for stage in STAGES:
        _prime_stage(stages_dir, stage)

    report = aggregate_q1.aggregate()
    expected = _manual_bundle(stages_dir)
    assert report["bundle"]["sha256"] == expected
