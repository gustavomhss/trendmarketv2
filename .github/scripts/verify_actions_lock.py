#!/usr/bin/env python3
"""Validate the structure and content of actions.lock."""

from __future__ import annotations

import json
import re
import sys
from datetime import datetime
from pathlib import Path
from typing import Any, Dict, Iterable, NoReturn

HEX40_RE = re.compile(r"^[0-9a-fA-F]{40}$")
ISO_DATETIME_RE = re.compile(r"^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z$")


def is_iso8601(value: str) -> bool:
    if not ISO_DATETIME_RE.fullmatch(value):
        return False
    try:
        datetime.fromisoformat(value.replace("Z", "+00:00"))
    except ValueError:
        return False
    return True


def fail(message: str) -> NoReturn:
    print(f"[fail] {message}")
    raise SystemExit(3)


def expect(condition: bool, message: str) -> None:
    if not condition:
        fail(message)


def ensure_fields(payload: Dict[str, Any], fields: Iterable[str], *, context: str) -> None:
    for field in fields:
        if field not in payload:
            fail(f"{context}: campo {field} ausente")
        if isinstance(payload[field], str) and not payload[field].strip():
            fail(f"{context}: campo {field} vazio")


def validate_action(action: Dict[str, Any], index: int) -> None:
    ensure_fields(
        action,
        ("repo", "ref", "sha", "date", "author", "rationale", "url"),
        context=f"actions[{index}]",
    )
    if not HEX40_RE.fullmatch(str(action["sha"])):
        fail(f"actions[{index}]: SHA inválido")
    if not is_iso8601(str(action["date"])):
        fail(f"actions[{index}]: date inválido")
    if not str(action["url"]).startswith("https://github.com/"):
        fail(f"actions[{index}]: url inválida")


def validate_lock(path: Path) -> None:
    if not path.exists():
        fail(f"Arquivo não encontrado: {path}")
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        fail(f"JSON inválido: {exc}")

    if not isinstance(payload, dict):
        fail("Formato inválido: esperado objeto na raiz")

    expect(payload.get("version") == 1, "Campo version ausente ou inválido")

    metadata = payload.get("metadata")
    if not isinstance(metadata, dict):
        fail("metadata: esperado objeto")
    ensure_fields(metadata, ("sha", "date", "author", "rationale"), context="metadata")
    if not HEX40_RE.fullmatch(str(metadata["sha"])):
        fail("metadata: SHA inválido")
    if not is_iso8601(str(metadata["date"])):
        fail("metadata: date inválido")

    actions = payload.get("actions")
    if not isinstance(actions, list) or not actions:
        fail("actions: lista vazia ou inválida")

    for index, action in enumerate(actions, start=1):
        if not isinstance(action, dict):
            fail(f"actions[{index}]: esperado objeto")
        validate_action(action, index)

    print("[ok] actions.lock válido")


def main() -> int:
    path = Path(sys.argv[1]) if len(sys.argv) > 1 else Path("actions.lock")
    validate_lock(path)
    return 0


if __name__ == "__main__":
    sys.exit(main())
