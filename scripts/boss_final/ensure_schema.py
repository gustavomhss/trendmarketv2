#!/usr/bin/env python3
"""Ensure Boss Final local report includes mandatory schema fields."""

from __future__ import annotations

import datetime
import json
import os
import pathlib
import re
from typing import Any, MutableMapping

MANDATORY = ("schema", "schema_version", "timestamp_utc", "generated_at", "status")


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


def ensure_schema_metadata(data: MutableMapping[str, Any]) -> bool:
    changed = False

    schema_version = data.get("schema_version")
    if not schema_version:
        data["schema_version"] = _schema_version_default()
    if not data.get("schema_version"):
        schema_env = os.environ.get("BOSS_SCHEMA_VERSION", "1")
        data["schema_version"] = schema_env.strip() or "1"
        changed = True

    version = _infer_version(data)

    schema_value = data.get("schema")
    if not isinstance(schema_value, str) or "boss_final.report@" not in schema_value:
        data["schema"] = f"boss_final.report@{version}"
        changed = True

    if str(data.get("schema_version")) != str(version):
        data["schema_version"] = str(version)
        changed = True

    timestamp = data.get("timestamp_utc")
    if not timestamp:
        data["timestamp_utc"] = _now_utc_z()
        timestamp = data["timestamp_utc"]
        changed = True

    if not data.get("generated_at"):
        data["generated_at"] = timestamp
        changed = True

    status = data.get("status")
    if isinstance(status, str) and status.strip():
        normalized = status.strip().upper()
        if normalized != status:
            data["status"] = normalized
            changed = True
    else:
    if not data.get("status"):
        default_status = (
            os.environ.get("BOSS_LOCAL_STATUS", "PASS").strip().upper() or "PASS"
        )
        data["status"] = default_status
        changed = True

    missing = [field for field in MANDATORY if field not in data]
    if missing:
        raise SystemExit(
            f"[ensure-schema] campos obrigatórios ausentes após normalização: {', '.join(missing)}"
        )

    return changed


def _ensure_fields(path: pathlib.Path) -> None:
    data = json.loads(path.read_text(encoding="utf-8"))
    changed = ensure_schema_metadata(data)

    if changed:
        path.write_text(
            json.dumps(data, ensure_ascii=False, indent=2) + "\n", encoding="utf-8"
        )

    print(
        f"[ensure-schema] OK: {path} | schema={data['schema']} | v={data['schema_version']} | ts={data['timestamp_utc']} | status={data['status']}"
    )


if __name__ == "__main__":
    _ensure_fields(_find_candidate())
