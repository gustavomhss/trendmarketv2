"""Regression tests for the local Boss Final aggregate generator."""

from __future__ import annotations

import json
import pathlib
import subprocess

import pytest

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


def _find_report() -> pathlib.Path:
    path = pathlib.Path("out/boss_final/report.local.json")
    if path.exists():
        return path
    candidates = sorted(pathlib.Path("out").rglob("report.local.json"))
    if not candidates:
        raise AssertionError("Relatório local não encontrado")
    return candidates[0]


def test_required_fields(
    tmp_path: pathlib.Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setenv("RUNNER_TEMP", str(tmp_path))
    out_dir = pathlib.Path("out/boss_final")
    if out_dir.exists():
        for item in out_dir.glob("report.local.json*"):
            item.unlink()
    out_dir.mkdir(parents=True, exist_ok=True)

    report_dir = tmp_path / "out" / "boss"
    report_dir.mkdir(parents=True)
    (report_dir / "report.json").write_text(json.dumps(sample), encoding="utf-8")
    monkeypatch.setenv("ARTS_DIR", str(report_dir.parent))

    subprocess.check_call(
        [
            "python",
            "scripts/boss_final/aggregate_reports_local.py",
        ]
    )

    report_path = _find_report()
    data = json.loads(report_path.read_text(encoding="utf-8"))
    assert data["schema"].startswith("boss_final.report@"), (
        "Campo `schema` ausente ou inválido"
    )
    assert isinstance(data.get("schema_version"), int) and data["schema_version"] > 0, (
        "Campo `schema_version` ausente ou inválido"
    )
    assert "generated_at" in data, "`generated_at` ausente"
    assert "timestamp_utc" in data, "`timestamp_utc` ausente"
    assert data.get("status") == "PASS", "`status` ausente ou inválido"
