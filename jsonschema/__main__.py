from __future__ import annotations

import argparse
import json
from pathlib import Path

from . import ValidationError, validate


def main() -> int:
    parser = argparse.ArgumentParser(description="Minimal jsonschema validator")
    parser.add_argument("--instance", required=True, help="Caminho do JSON a validar")
    parser.add_argument("--schema", required=True, help="Caminho do schema JSON")
    args = parser.parse_args()
    instance_path = Path(args.instance)
    schema_path = Path(args.schema)
    instance = json.loads(instance_path.read_text(encoding="utf-8"))
    schema = json.loads(schema_path.read_text(encoding="utf-8"))
    try:
        validate(instance, schema)
    except ValidationError as exc:
        print(f"ValidationError: {exc.message}")
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
