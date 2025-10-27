"""Regression tests for the local Boss Final aggregate generator."""

from __future__ import annotations

import json
import pathlib
import subprocess


def _find_report() -> pathlib.Path:
    path = pathlib.Path("out/boss_final/report.local.json")
    if path.exists():
        return path
    candidates = sorted(pathlib.Path("out").rglob("report.local.json"))
    if not candidates:
        raise AssertionError("Relatório local não encontrado")
    return candidates[0]


def test_local_aggregate_has_schema(tmp_path, monkeypatch) -> None:
    monkeypatch.setenv("RUNNER_TEMP", str(tmp_path))
    out_dir = pathlib.Path("out/boss_final")
    if out_dir.exists():
        for item in out_dir.glob("report.local.json*"):
            item.unlink()
    out_dir.mkdir(parents=True, exist_ok=True)

    arts_dir = tmp_path / "boss-arts"
    arts_dir.mkdir()
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
    report_dir = arts_dir / "stage" / "one"
    report_dir.mkdir(parents=True)
    (report_dir / "report.json").write_text(json.dumps(sample), encoding="utf-8")

    subprocess.check_call([
        "python",
        "scripts/boss_final/aggregate_reports_local.py",
    ])

    report_path = _find_report()
    data = json.loads(report_path.read_text(encoding="utf-8"))
    assert data["schema"].startswith("boss_final.report@"), "Campo `schema` ausente ou inválido"
    assert "generated_at" in data, "`generated_at` ausente"
