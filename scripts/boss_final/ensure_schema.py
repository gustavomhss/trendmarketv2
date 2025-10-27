#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import pathlib
from datetime import datetime, timezone


def _find_candidate(root: pathlib.Path = pathlib.Path("out")) -> pathlib.Path:
    candidates = sorted(root.rglob("report.local.json"))
    if not candidates:
        raise SystemExit(
            "[ensure-schema] relatório não encontrado: out/boss_final/report.local.json"
        )
    return candidates[0]


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Ensure Boss Final local aggregate report declares schema metadata."
    )
    parser.add_argument(
        "report",
        nargs="?",
        type=pathlib.Path,
        default=None,
        help="Optional explicit report.local.json path.",
    )
    args = parser.parse_args()

    path = args.report if args.report and args.report.exists() else _find_candidate()
    data = json.loads(path.read_text(encoding="utf-8"))
    changed = False

    if (
        "schema" not in data
        or not isinstance(data["schema"], str)
        or not data["schema"]
    ):
        data["schema"] = "boss_final.report@1"
        changed = True

    if "generated_at" not in data:
        data["generated_at"] = datetime.now(timezone.utc).isoformat()
        changed = True

    if changed:
        path.write_text(
            json.dumps(data, ensure_ascii=False, indent=2) + "\n",
            encoding="utf-8",
        )

    print(f"[ensure-schema] OK: {path} | schema: {data['schema']}")


if __name__ == "__main__":
    main()
