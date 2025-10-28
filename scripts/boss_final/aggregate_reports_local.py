#!/usr/bin/env python3
"""Aggregate guard stage reports from local artifacts."""

from __future__ import annotations

import hashlib
import json
import os
import re
import shutil
import zipfile
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, List

try:  # Compatibilidade execução via módulo ou script
    from ensure_schema import ensure_schema_metadata
except ImportError:  # pragma: no cover - fallback para execução via pacote
    from .ensure_schema import ensure_schema_metadata  # type: ignore

RUNNER_TEMP = Path(os.environ.get("RUNNER_TEMP", "."))
ARTS_DIR = Path(os.environ.get("ARTS_DIR") or RUNNER_TEMP / "boss-arts")
OUT_DIR = Path(os.environ.get("REPORT_DIR") or RUNNER_TEMP / "boss-aggregate")


def _sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def _build_or_locate_bundle(out_dir: Path) -> Path | None:
    out_dir.mkdir(parents=True, exist_ok=True)
    bundle = out_dir / "boss-final-bundle.zip"
    if bundle.exists():
        return bundle
    stage_zips = sorted(out_dir.glob("boss-stage-*.zip"))
    if not stage_zips:
        return None
    with zipfile.ZipFile(bundle, "w", compression=zipfile.ZIP_DEFLATED) as archive:
        for stage_zip in stage_zips:
            archive.write(stage_zip, arcname=stage_zip.name)
    return bundle


def _load_report(path: Path) -> List[Dict[str, Any]]:
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except Exception as exc:  # noqa: BLE001 - safe aggregation
        return [{"name": "unknown", "status": "error", "errors": [str(exc)]}]
    if isinstance(data, dict) and isinstance(data.get("stages"), list):
        return [entry for entry in data["stages"] if isinstance(entry, dict)]
    return []


def collect_stage_results(root: Path) -> List[Dict[str, Any]]:
    results: List[Dict[str, Any]] = []
    if not root.exists():
        return results
    for report_path in root.rglob("report.json"):
        results.extend(_load_report(report_path))
    return results


def ensure_missing_stages(results: List[Dict[str, Any]]) -> None:
    present = {entry.get("name") for entry in results}
    for index in range(1, 7):
        name = f"s{index}"
        if name not in present:
            results.append(
                {"name": name, "status": "missing", "errors": ["artifact not found"]}
            )


def write_aggregate(results: List[Dict[str, Any]]) -> Dict[str, Any]:
    aggregate: Dict[str, Any] = {"stages": results}

    summary = summarize_status(results)
    aggregate["status"] = summary["status"]
    aggregate["summary"] = summary

    version: int | None = None
    schema_raw = aggregate.get("schema")
    if isinstance(schema_raw, str):
        match = re.search(r"@(\d+)$", schema_raw)
        if match:
            try:
                version = int(match.group(1))
            except Exception:  # noqa: BLE001 - defensive parsing
                version = None
    if version is None:
        schema_version_raw = aggregate.get("schema_version")
        try:
            version = int(str(schema_version_raw))
        except Exception:
            version = None
    if version is None:
        version = 1

    now = (
        datetime.now(timezone.utc)
        .replace(microsecond=0)
        .isoformat()
        .replace("+00:00", "Z")
    )
    aggregate["schema"] = f"boss_final.report@{version}"
    aggregate["schema_version"] = version
    aggregate.setdefault("timestamp_utc", now)
    aggregate.setdefault("generated_at", aggregate["timestamp_utc"])

    return aggregate


def summarize_status(results: List[Dict[str, Any]]) -> Dict[str, Any]:
    status = {
        entry["name"]: str(entry.get("status", "missing")).upper()
        for entry in results
        if "name" in entry
    }
    overall = "FAIL" if any(value != "PASSED" for value in status.values()) else "PASS"
    return {"status": overall, "stages": status}


def extract_stage_archives(arts_dir: Path, boss_out_dir: Path) -> None:
    arts_dir.mkdir(parents=True, exist_ok=True)
    for archive_path in sorted(boss_out_dir.glob("boss-stage-*.zip")):
        target = arts_dir / archive_path.stem
        try:
            if target.exists():
                continue
            target.mkdir(parents=True, exist_ok=True)
            with zipfile.ZipFile(archive_path) as archive:
                archive.extractall(target)
        except zipfile.BadZipFile as exc:
            print(f"[aggregate-local] zip inválido: {archive_path}: {exc}")
        except OSError as exc:
            print(f"[aggregate-local] falha ao extrair {archive_path}: {exc}")


def main() -> int:
    boss_out_dir = Path(os.environ.get("BOSS_OUT_DIR", "out/boss"))
    boss_out_dir.mkdir(parents=True, exist_ok=True)

    stage_glob = os.environ.get("BOSS_STAGE_GLOB", "boss-stage-*.zip")
    stage_dir_env = os.environ.get("BOSS_STAGE_DIR")
    search_roots: list[Path] = []
    if stage_dir_env:
        search_roots.append(Path(stage_dir_env))
    search_roots.append(Path.cwd())

    for root in search_roots:
        if not root.exists():
            continue
        for candidate in root.rglob(stage_glob):
            target = boss_out_dir / candidate.name
            try:
                if target.exists() or candidate.resolve() == target.resolve():
                    continue
            except OSError:
                if target.exists():
                    continue
            try:
                shutil.copy2(candidate, target)
            except Exception as exc:  # noqa: BLE001 - logging defensivo
                print(
                    f"[aggregate-local] aviso ao copiar zips: {candidate} -> {target}: {exc}"
                )

    extract_stage_archives(ARTS_DIR, boss_out_dir)

    results = collect_stage_results(ARTS_DIR)
    ensure_missing_stages(results)
    aggregate = write_aggregate(results)

    os.environ.setdefault("BOSS_OUT_DIR", str(boss_out_dir))
    os.environ.setdefault("BOSS_STAGE_GLOB", stage_glob)

    bundle_path = _build_or_locate_bundle(boss_out_dir)
    if "bundle" not in aggregate and bundle_path and bundle_path.exists():
        aggregate["bundle"] = {
            "path": str(bundle_path),
            "sha256": _sha256(bundle_path),
            "size_bytes": bundle_path.stat().st_size,
        }

    report = ensure_schema_metadata(aggregate)

    payload = json.dumps(report, ensure_ascii=False, indent=2) + "\n"

    OUT_DIR.mkdir(parents=True, exist_ok=True)
    (OUT_DIR / "report.json").write_text(payload, encoding="utf-8")

    local_dir = Path("out/boss_final")
    local_dir.mkdir(parents=True, exist_ok=True)
    (local_dir / "report.local.json").write_text(payload, encoding="utf-8")

    boss_out_dir.mkdir(parents=True, exist_ok=True)
    (boss_out_dir / "boss-final-report.json").write_text(payload, encoding="utf-8")

    summary = report.get("summary", summarize_status(results))
    print(json.dumps(summary))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
