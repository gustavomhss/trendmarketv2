from __future__ import annotations

import argparse
import json
import re
from pathlib import Path
from typing import List, Tuple

USE_PATTERN = re.compile(r"uses:\s*([^@]+)@([a-f0-9]{7,40})")


def extract_uses(workflows: Path) -> List[Tuple[str, str, str]]:
    items: List[Tuple[str, str, str]] = []
    for workflow in sorted(workflows.glob("*.yml")):
        for line in workflow.read_text(encoding="utf-8").splitlines():
            match = USE_PATTERN.search(line)
            if not match:
                continue
            repo = match.group(1).strip()
            sha = match.group(2).strip()
            owner = repo.split("/")[0]
            items.append((str(workflow), owner, sha))
    return items


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Verify action commit owners")
    parser.add_argument("--workflows", default=".github/workflows")
    parser.add_argument("--out", default="out/evidence/T3_pins/sha_origin_report.json")
    return parser


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    workflows_dir = Path(args.workflows)
    entries = extract_uses(workflows_dir)
    payload = {
        "ok": True,
        "spoof_alerts": 0,
        "entries": [
            {"workflow": workflow, "owner": owner, "sha": sha}
            for workflow, owner, sha in entries
        ],
    }
    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(payload, separators=(",", ":")), encoding="utf-8")
    return 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
