from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

from . import Draft7Validator, FormatChecker, ValidationError


def _load_json(path: Path) -> object:
    try:
        text = path.read_text(encoding="utf-8")
    except FileNotFoundError:
        print(f"jsonschema: arquivo não encontrado: {path}", file=sys.stderr)
        raise SystemExit(2)
    except OSError as exc:
        print(f"jsonschema: erro ao ler {path}: {exc}", file=sys.stderr)
        raise SystemExit(2)
    try:
        return json.loads(text)
    except json.JSONDecodeError as exc:
        print(f"jsonschema: JSON inválido em {path}: {exc}", file=sys.stderr)
        raise SystemExit(2)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(prog="python -m jsonschema")
    parser.add_argument("--instance", required=True, type=Path)
    parser.add_argument("--schema", required=True, type=Path)
    args = parser.parse_args(argv)

    instance = _load_json(args.instance)
    schema_obj = _load_json(args.schema)
    validator = Draft7Validator(schema_obj, format_checker=FormatChecker())
    try:
        validator.validate(instance)
    except ValidationError as exc:
        location = "/".join(str(part) for part in exc.path)
        suffix = f" (campo {location})" if location else ""
        print(f"jsonschema: falha de validação{suffix}: {exc.message}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
