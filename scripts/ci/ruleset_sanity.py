from __future__ import annotations

import argparse
import json
import os
import time
from pathlib import Path
from typing import Iterable, List, Sequence

REQUIRED_CONTEXTS = [
    "S7 ORR Exec / t0_ruleset_sanity",
    "S7 ORR Exec / t1_yaml",
    "S7 ORR Exec / t2_security",
    "S7 ORR Exec / t3_pins",
    "S7 ORR Exec / t4_tests",
    "S7 ORR Exec / t5_props",
    "S7 ORR Exec / t6_determinism",
    "S7 ORR Exec / t7_append_only",
    "S7 ORR Exec / t8_pack",
]


class RulesetError(RuntimeError):
    def __init__(self, message: str, exit_code: int) -> None:
        super().__init__(message)
        self.exit_code = exit_code


def parse_contexts(raw: str) -> List[str]:
    return [item.strip() for item in raw.split(",") if item.strip()]


def load_contexts(path: Path | None) -> Sequence[str]:
    if path and path.exists():
        data = json.loads(path.read_text(encoding="utf-8"))
        if isinstance(data, dict) and "contexts" in data:
            return list(data["contexts"])
        if isinstance(data, list):
            return list(data)
        raise RulesetError("invalid_contexts_file", 3)
    env_contexts = os.environ.get("S7_REQUIRED_CONTEXTS")
    if env_contexts:
        return parse_contexts(env_contexts)
    return REQUIRED_CONTEXTS


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Validate GitHub ruleset required contexts")
    parser.add_argument("--out", default="out/evidence/T0_ruleset_sanity/ruleset_check.json")
    parser.add_argument("--contexts")
    return parser


def main(argv: Iterable[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(list(argv) if argv is not None else None)
    start = time.monotonic()
    contexts = load_contexts(Path(args.contexts) if args.contexts else None)
    missing = sorted(set(REQUIRED_CONTEXTS) - set(contexts))
    extra = sorted(set(contexts) - set(REQUIRED_CONTEXTS))
    duration_ms = int((time.monotonic() - start) * 1000)
    payload = {
        "ok": not missing and not extra,
        "required_contexts": list(contexts),
        "missing": missing,
        "extra": extra,
        "duration_ms": duration_ms,
    }
    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(payload, separators=(",", ":")), encoding="utf-8")
    if missing:
        return 2
    if extra:
        return 2
    return 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
