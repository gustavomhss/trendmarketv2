#!/usr/bin/env python3
"""Ensure Boss Final local report includes mandatory schema fields."""

from __future__ import annotations
import json
import pathlib
import re
from datetime import datetime, timezone


def _find_candidate() -> pathlib.Path:
    candidates = sorted(pathlib.Path("out").rglob("report.local.json"))
    if not candidates:
        raise SystemExit(
            "[ensure-schema] relatório não encontrado: out/boss_final/report.local.json"
        )
    return candidates[0]


def _ensure_fields(path: pathlib.Path) -> None:
    data = json.loads(path.read_text(encoding="utf-8"))
    changed = False
    now = datetime.now(timezone.utc).replace(microsecond=0)
    ts = now.isoformat().replace("+00:00", "Z")

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
    if version is None:
        version = 1

    if not isinstance(s, str) or "boss_final.report@" not in s:
        data["schema"] = f"boss_final.report@{version}"
        changed = True
    if str(data.get("schema_version")) != str(version):
        data["schema_version"] = version
        changed = True
    if not data.get("timestamp_utc"):
        data["timestamp_utc"] = ts
        changed = True
    if not data.get("generated_at"):
        data["generated_at"] = data["timestamp_utc"]
        changed = True

    if changed:
        path.write_text(
            json.dumps(data, ensure_ascii=False, indent=2) + "\n", encoding="utf-8"
        )
    print(
        f"[ensure-schema] OK: {path} | schema={data['schema']} | schema_version={data['schema_version']} | timestamp_utc={data['timestamp_utc']}"
    )


if __name__ == "__main__":
    _ensure_fields(_find_candidate())
