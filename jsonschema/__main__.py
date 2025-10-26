from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

from . import Draft7Validator, ValidationError


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Minimal jsonschema validator")
    parser.add_argument("--instance", required=True)
    parser.add_argument("--schema", required=True)
    args = parser.parse_args(argv)

    instance_path = Path(args.instance)
    schema_path = Path(args.schema)
    instance = json.loads(instance_path.read_text(encoding="utf-8"))
    schema = json.loads(schema_path.read_text(encoding="utf-8"))

    validator = Draft7Validator(schema)
    try:
        validator.validate(instance)
    except ValidationError as exc:
        location = "/".join(str(part) for part in exc.path)
        message = exc.message if location == "" else f"{exc.message} at {location}"
        print(message, file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main(sys.argv[1:]))
