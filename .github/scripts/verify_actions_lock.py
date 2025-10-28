#!/usr/bin/env python3
"""Validate the structure and content of actions.lock."""

from __future__ import annotations
import argparse
import json
import re
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, Iterable, NoReturn, Sequence

HEX40_RE = re.compile(r"^[0-9a-fA-F]{40}$")
ISO_DATETIME_RE = re.compile(r"^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z$")


class ValidationError(RuntimeError):
    """Raised when the lock file violates the required contract."""


def isoformat_now() -> str:
    return (
        datetime.now(timezone.utc)
        .replace(microsecond=0)
        .isoformat()
        .replace("+00:00", "Z")
    )


def is_iso8601(value: str) -> bool:
    if not ISO_DATETIME_RE.fullmatch(value):
        return False
    try:
        datetime.fromisoformat(value.replace("Z", "+00:00"))
    except ValueError:
        return False
    return True


def fail(message: str) -> NoReturn:
    raise ValidationError(message)


def expect(condition: bool, message: str) -> None:
    if not condition:
        fail(message)


def ensure_fields(
    payload: Dict[str, Any], fields: Iterable[str], *, context: str
) -> None:
    for field in fields:
        if field not in payload:
            fail(f"{context}: campo {field} ausente")
        if isinstance(payload[field], str) and not payload[field].strip():
            fail(f"{context}: campo {field} vazio")


def write_report(report_path: Path, payload: Dict[str, Any]) -> None:
    report_path.parent.mkdir(parents=True, exist_ok=True)
    report_path.write_text(
        json.dumps(payload, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )


def validate_action(action: Dict[str, Any], index: int) -> Dict[str, Any]:
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
    return {
        "repo": action["repo"],
        "ref": action["ref"],
        "sha": action["sha"],
        "date": action["date"],
        "author": action["author"],
        "rationale": action["rationale"],
        "url": action["url"],
    }


def validate_lock(path: Path) -> Dict[str, Any]:
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

    validated_actions = []
    for index, action in enumerate(actions, start=1):
        if not isinstance(action, dict):
            fail(f"actions[{index}]: esperado objeto")
        validated_actions.append(validate_action(action, index))

    return {
        "path": str(path),
        "version": payload.get("version"),
        "metadata": metadata,
        "actions_count": len(validated_actions),
        "actions": validated_actions,
    }


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Validate actions.lock contents")
    parser.add_argument("path", nargs="?", default="actions.lock")
    parser.add_argument(
        "--report",
        default="out/guard/s4/actions_lock_report.json",
        help="Arquivo de saída para o relatório JSON",
    )
    args = parser.parse_args(argv)

    path = Path(args.path)
    report_path = Path(args.report)
    try:
        result = validate_lock(path)
    except ValidationError as exc:
        payload = {
            "status": "fail",
            "path": str(path),
            "timestamp_utc": isoformat_now(),
            "error": str(exc),
        }
        write_report(report_path, payload)
        print(f"[fail] {exc}")
        return 3

    result.update(
        {
            "status": "pass",
            "timestamp_utc": isoformat_now(),
        }
    )
    write_report(report_path, result)
    print("[ok] actions.lock válido")
    return 0


if __name__ == "__main__":
    sys.exit(main())
