#!/usr/bin/env python3
"""Ensure Boss Final local report includes mandatory schema fields."""

from __future__ import annotations

import datetime
import hashlib
import json
import os
import pathlib
import re
import sys
import zipfile
from typing import Any, MutableMapping

MANDATORY = ("schema", "schema_version", "timestamp_utc", "generated_at", "status")


def _sha256(path: pathlib.Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def _find_stage_zips(
    search_roots: list[pathlib.Path], pattern: str
) -> list[pathlib.Path]:
    found: list[pathlib.Path] = []
    for root in search_roots:
        if not root.exists():
            continue
        found.extend(root.glob(pattern))
        found.extend(root.rglob(pattern))
    unique = sorted({path.resolve() for path in found if path.is_file()})
    return unique


def _find_candidate() -> pathlib.Path:
    candidates = sorted(pathlib.Path("out").rglob("report.local.json"))
    if not candidates:
        raise SystemExit(
            "[ensure-schema] relatório não encontrado: out/boss_final/report.local.json"
        )
    return candidates[0]


def _schema_version_default() -> int:
    raw = os.environ.get("BOSS_SCHEMA_VERSION", "1")
    try:
        return int(raw.strip() or "1")
    except (TypeError, ValueError):
        return 1


def _infer_version(data: MutableMapping[str, Any]) -> int:
    version = None
    s = data.get("schema")
    if isinstance(s, str):
        m = re.search(r"@(\d+)$", s)
        if m:
            try:
                version = int(m.group(1))
            except Exception:
                version = None
    if version is None:
        try:
            version = int(str(data.get("schema_version")))
        except Exception:
            version = None
    return version or _schema_version_default()


def _now_utc_z() -> str:
    return (
        datetime.datetime.now(datetime.timezone.utc)
        .replace(microsecond=0)
        .isoformat()
        .replace("+00:00", "Z")
    )


def ensure_schema_metadata(data: MutableMapping[str, Any]) -> dict[str, Any]:
    """Normalize Boss Final reports enforcing local contracts."""

    normalized: dict[str, Any] = dict(data)

    schema_version = normalized.get("schema_version")
    if not schema_version:
        normalized["schema_version"] = _schema_version_default()

    version = _infer_version(normalized)

    schema_value = normalized.get("schema")
    if not isinstance(schema_value, str) or "boss_final.report@" not in schema_value:
        normalized["schema"] = f"boss_final.report@{version}"

    if str(normalized.get("schema_version")) != str(version):
        normalized["schema_version"] = int(version)

    timestamp = normalized.get("timestamp_utc")
    if not timestamp:
        normalized["timestamp_utc"] = _now_utc_z()
        timestamp = normalized["timestamp_utc"]

    if not normalized.get("generated_at"):
        normalized["generated_at"] = timestamp

    status = normalized.get("status")
    if isinstance(status, str) and status.strip():
        normalized["status"] = status.strip().upper()
    else:
        default_status = (
            os.environ.get("BOSS_LOCAL_STATUS", "PASS").strip().upper() or "PASS"
        )
        normalized["status"] = default_status

    bundle_info = normalized.get("bundle")
    required_bundle_keys = {"path", "sha256", "size_bytes"}
    has_complete_bundle = isinstance(
        bundle_info, MutableMapping
    ) and required_bundle_keys.issubset(bundle_info.keys())

    boss_out_dir = pathlib.Path(os.environ.get("BOSS_OUT_DIR", "out/boss"))
    bundle_override = os.environ.get("BOSS_BUNDLE_PATH")
    stage_dir_override = os.environ.get("BOSS_STAGE_DIR")
    stage_glob = os.environ.get("BOSS_STAGE_GLOB", "boss-stage-*.zip")
    bundle_name = os.environ.get("BOSS_BUNDLE_NAME", "boss-final-bundle.zip")
    bundle_path = boss_out_dir / bundle_name

    if has_complete_bundle:
        bundle_path = pathlib.Path(str(bundle_info["path"]))
        if not bundle_path.exists():
            print("[ensure-schema] bundle.path informado não existe no filesystem")
            sys.exit(1)
        normalized["bundle"] = {
            "path": str(bundle_path),
            "sha256": _sha256(bundle_path),
            "size_bytes": bundle_path.stat().st_size,
        }
        return normalized

    chosen_bundle: pathlib.Path | None = None

    if bundle_override:
        override_path = pathlib.Path(bundle_override)
        if override_path.exists():
            chosen_bundle = override_path
        else:
            print(
                f"[ensure-schema] BOSS_BUNDLE_PATH aponta para arquivo inexistente: {override_path}"
            )

    if chosen_bundle is None and isinstance(bundle_info, MutableMapping):
        raw_bundle_path = bundle_info.get("path")
        if raw_bundle_path:
            bundle_path_candidate = pathlib.Path(str(raw_bundle_path))
            if bundle_path_candidate.exists():
                chosen_bundle = bundle_path_candidate

    if chosen_bundle is None:
        search_roots: list[pathlib.Path] = []
        if stage_dir_override:
            search_roots.append(pathlib.Path(stage_dir_override))
        search_roots.append(boss_out_dir)
        search_roots.append(pathlib.Path.cwd())

        stage_zips = _find_stage_zips(search_roots, stage_glob)
        if stage_zips:
            bundle_path.parent.mkdir(parents=True, exist_ok=True)
            print(f"[ensure-schema] Zips de estágio detectados ({len(stage_zips)}):")
            for stage_zip in stage_zips:
                print(f"  - {stage_zip}")
            with zipfile.ZipFile(
                bundle_path, "w", compression=zipfile.ZIP_DEFLATED
            ) as archive:
                for stage_zip in stage_zips:
                    archive.write(stage_zip, arcname=stage_zip.name)
            chosen_bundle = bundle_path
        else:
            print(
                "[ensure-schema] Nenhum boss-stage-*.zip encontrado (roots verificados):"
            )
            for root in search_roots:
                print(f"  - {root}")

    if chosen_bundle is None:
        print("[ensure-schema] bundle ausente e não foi possível inferir")
        sys.exit(1)

    normalized["bundle"] = {
        "path": str(chosen_bundle),
        "sha256": _sha256(chosen_bundle),
        "size_bytes": chosen_bundle.stat().st_size,
    }

    missing = [field for field in MANDATORY if field not in normalized]
    if missing:
        raise SystemExit(
            f"[ensure-schema] campos obrigatórios ausentes após normalização: {', '.join(missing)}"
        )

    return normalized


def _ensure_fields(path: pathlib.Path) -> None:
    data = json.loads(path.read_text(encoding="utf-8"))
    normalized = ensure_schema_metadata(data)

    if normalized != data:
        path.write_text(
            json.dumps(normalized, ensure_ascii=False, indent=2) + "\n",
            encoding="utf-8",
        )
    data = normalized

    print(
        f"[ensure-schema] OK: {path} | schema={data['schema']} | v={data['schema_version']} | ts={data['timestamp_utc']} | status={data['status']}"
    )


def main() -> int:
    _ensure_fields(_find_candidate())
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
