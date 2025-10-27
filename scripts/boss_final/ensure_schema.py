#!/usr/bin/env python3
"""Ensure the local Boss Final aggregate report declares its schema."""

from __future__ import annotations

import datetime
import json
import pathlib
import sys


def _default_path() -> pathlib.Path:
    return pathlib.Path("out/boss_final/report.local.json")


def _find_candidate() -> pathlib.Path:
    candidates = sorted(pathlib.Path("out").rglob("report.local.json"))
    if not candidates:
        raise SystemExit("[ensure-schema] relatório não encontrado: out/boss_final/report.local.json")
    return candidates[0]


def main() -> None:
    target_arg = pathlib.Path(sys.argv[1]) if len(sys.argv) > 1 else _default_path()
    path = target_arg if target_arg.exists() else _find_candidate()

    data = json.loads(path.read_text(encoding="utf-8"))
    changed = False
    if "schema" not in data:
        data["schema"] = "boss_final.report@v1"
        changed = True
    if "generated_at" not in data:
        data["generated_at"] = (
            datetime.datetime.utcnow().replace(microsecond=0).isoformat() + "Z"
        )
        changed = True

    if changed:
        path.write_text(json.dumps(data, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")

    print(f"[ensure-schema] OK: {path} | schema: {data['schema']}")


if __name__ == "__main__":  # pragma: no cover
    main()
