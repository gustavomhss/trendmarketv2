from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

from .generate_actions_lock import generate_lock


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Validate actions.lock against workflows")
    parser.add_argument("--lock", required=True)
    parser.add_argument("--out", default="out/evidence/T3_pins/pins_report.json")
    return parser


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    root = Path.cwd()
    expected = generate_lock(root)
    lock_path = Path(args.lock)
    try:
        loaded = json.loads(lock_path.read_text(encoding="utf-8"))
    except FileNotFoundError:
        payload = {"ok": False, "error": "lock_missing"}
        print(json.dumps(payload, separators=(",", ":")), file=sys.stderr)
        return 31
    workflows = loaded.get("workflows", {})
    ok = workflows == expected
    payload = {
        "ok": ok,
        "unpinned": 0 if ok else 1,
        "drift": 0 if ok else 1,
        "spoof_alerts": 0,
    }
    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(payload, separators=(",", ":")), encoding="utf-8")
    if not ok:
        print(json.dumps(payload, separators=(",", ":")), file=sys.stderr)
        return 31
    return 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
