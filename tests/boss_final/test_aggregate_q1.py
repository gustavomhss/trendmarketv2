from __future__ import annotations

import json
from pathlib import Path

import pytest

from scripts.boss_final import aggregate_q1

BASE_DIR = Path(__file__).resolve().parents[2]
STAGES_DIR = BASE_DIR / "out" / "q1_boss_final" / "stages"
OUTPUT_DIR = BASE_DIR / "out" / "q1_boss_final"


@pytest.fixture(autouse=True)
def cleanup() -> None:
    if OUTPUT_DIR.exists():
        for path in OUTPUT_DIR.rglob('*'):
            if path.is_file():
                path.unlink()
        for path in sorted(OUTPUT_DIR.rglob('*'), reverse=True):
            if path.is_dir():
                path.rmdir()
    if STAGES_DIR.exists():
        for path in STAGES_DIR.rglob('*'):
            if path.is_file():
                path.unlink()
        for path in sorted(STAGES_DIR.rglob('*'), reverse=True):
            if path.is_dir():
                path.rmdir()
    yield
    if OUTPUT_DIR.exists():
        for path in OUTPUT_DIR.rglob('*'):
            if path.is_file():
                path.unlink()
        for path in sorted(OUTPUT_DIR.rglob('*'), reverse=True):
            if path.is_dir():
                path.rmdir()
    if STAGES_DIR.exists():
        for path in STAGES_DIR.rglob('*'):
            if path.is_file():
                path.unlink()
        for path in sorted(STAGES_DIR.rglob('*'), reverse=True):
            if path.is_dir():
                path.rmdir()


def _write_stage(stage: str, status: str, notes: str) -> None:
    stage_dir = STAGES_DIR / stage
    stage_dir.mkdir(parents=True, exist_ok=True)
    (stage_dir / "guard_status.txt").write_text(f"{status}\n", encoding="utf-8")
    payload = {
        "stage": stage,
        "status": status,
        "timestamp_utc": "2024-09-30T07:00:00Z",
        "notes": notes,
    }
    (stage_dir / "stage.json").write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def test_aggregate_q1_pass() -> None:
    for stage in aggregate_q1.STAGES:
        _write_stage(stage, "PASS", f"{stage} ok")

    result = aggregate_q1.main()

    assert result == 0
    report = json.loads((OUTPUT_DIR / "report.json").read_text(encoding="utf-8"))
    assert report["status"] == "PASS"
    assert report["sprints"]["s3"]["notes"] == "s3 ok"
    assert (OUTPUT_DIR / "guard_status.txt").read_text(encoding="utf-8").strip() == "PASS"


def test_stage_status_mismatch_triggers_fail() -> None:
    for stage in aggregate_q1.STAGES:
        status = "PASS"
        notes = "ok"
        _write_stage(stage, status, notes)
    # Break guard file for s4
    (STAGES_DIR / "s4" / "guard_status.txt").write_text("FAIL\n", encoding="utf-8")

    with pytest.raises(SystemExit):
        aggregate_q1.main()

    assert (OUTPUT_DIR / "guard_status.txt").read_text(encoding="utf-8").strip() == "FAIL"
