#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import pathlib
import re
from datetime import datetime, timezone
from typing import Any, Dict

SCHEMA_PREFIX = "boss_final.report"
DEFAULT_VERSION = 1
SCHEMA_PATTERN = re.compile(rf"^{re.escape(SCHEMA_PREFIX)}@(\d+)$")


def _default_schema() -> str:
    return f"{SCHEMA_PREFIX}@{DEFAULT_VERSION}"


def _extract_version(schema: object) -> int | None:
    if not isinstance(schema, str):
        return None
    candidate = schema.strip()
    if not candidate:
        return None
    match = SCHEMA_PATTERN.fullmatch(candidate)
    if not match:
        return None
    try:
        return int(match.group(1))
    except ValueError:
        return None


def ensure_schema_metadata(payload: Dict[str, Any]) -> bool:
    """Ensure schema fields are present and consistent."""

    changed = False
    version = _extract_version(payload.get("schema"))

    if version is None:
        payload["schema"] = _default_schema()
        version = DEFAULT_VERSION
        changed = True
    else:
        normalized_schema = f"{SCHEMA_PREFIX}@{version}"
        if payload.get("schema") != normalized_schema:
            payload["schema"] = normalized_schema
            changed = True

    if payload.get("schema_version") != version:
        payload["schema_version"] = version
        changed = True

    return changed


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
    changed = ensure_schema_metadata(data)

    if "generated_at" not in data:
        data["generated_at"] = datetime.now(timezone.utc).isoformat()
        changed = True

    if changed:
        path.write_text(
            json.dumps(data, ensure_ascii=False, indent=2) + "\n",
            encoding="utf-8",
        )

    print(
        "[ensure-schema] OK: %s | schema: %s | schema_version: %s"
        % (path, data["schema"], data.get("schema_version"))
    )


if __name__ == "__main__":
    main()
