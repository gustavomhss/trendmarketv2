"""Regression tests for the local Boss Final aggregate generator."""

from __future__ import annotations

import json
import pathlib
import re
import shutil
import subprocess
import zipfile

import pytest

from scripts.boss_final.ensure_schema import (
    expected_schema_id,
    expected_schema_version,
)

sample = {
    "stages": [
        {"name": "s1", "status": "PASSED"},
        {"name": "s2", "status": "PASSED"},
        {"name": "s3", "status": "PASSED"},
        {"name": "s4", "status": "PASSED"},
        {"name": "s5", "status": "PASSED"},
        {"name": "s6", "status": "PASSED"},
    ]
}


def _prepare_stage_archives(out_dir: pathlib.Path) -> None:
    if out_dir.exists():
        shutil.rmtree(out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    for index in range(1, 7):
        bundle = out_dir / f"boss-stage-s{index}.zip"
        with zipfile.ZipFile(bundle, "w", compression=zipfile.ZIP_DEFLATED) as archive:
            archive.writestr("status.txt", f"stage s{index}\n")


def test_required_fields(
    tmp_path: pathlib.Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setenv("RUNNER_TEMP", str(tmp_path))
    boss_out_dir = tmp_path / "boss-final"
    monkeypatch.setenv("BOSS_OUT_DIR", str(boss_out_dir))
    monkeypatch.setenv("REPORT_DIR", str(tmp_path / "aggregate"))

    _prepare_stage_archives(boss_out_dir)

    report_dir = tmp_path / "out" / "boss"
    report_dir.mkdir(parents=True)
    (report_dir / "report.json").write_text(json.dumps(sample), encoding="utf-8")
    monkeypatch.setenv("ARTS_DIR", str(report_dir.parent))

    subprocess.check_call(
        ["python", "scripts/boss_final/aggregate_reports_local.py"],
    )

    final_report = boss_out_dir / "boss-final-report.json"
    assert final_report.exists()
    data = json.loads(final_report.read_text(encoding="utf-8"))
    assert data["schema"] == expected_schema_id(), "Campo `schema` inválido"
    assert (
        isinstance(data.get("schema_version"), int)
        and data["schema_version"] == expected_schema_version()
    ), "Campo `schema_version` ausente ou inválido"
    assert "generated_at" not in data, "`generated_at` não deve estar presente"
    assert "summary" not in data, "`summary` não deve estar presente"
    assert "timestamp_utc" in data, "`timestamp_utc` ausente"
    assert data.get("status") == "PASS", "`status` ausente ou inválido"
    bundle = data.get("bundle") or {}
    assert set(bundle.keys()) == {"sha256"}
    assert re.fullmatch(r"[0-9a-f]{64}", bundle["sha256"]) is not None
    expected_bundle = boss_out_dir / "boss-final-bundle.zip"
    assert expected_bundle.exists()
    assert expected_bundle.stat().st_size > 0

    summary_path = boss_out_dir / "summary.md"
    assert summary_path.exists(), "summary.md deve ser gerado"
    summary_text = summary_path.read_text(encoding="utf-8")
    assert "Boss Final" in summary_text
    assert "Gerado em" in summary_text

    subprocess.check_call(
        ["python", "scripts/boss_final/aggregate_reports_local.py"],
    )

    rerun = json.loads(final_report.read_text(encoding="utf-8"))
    assert rerun["bundle"]["sha256"] == bundle["sha256"]
