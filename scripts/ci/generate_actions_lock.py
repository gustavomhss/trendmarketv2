from __future__ import annotations

import json
import re
import sys
from pathlib import Path
from typing import Dict, List, Tuple

USE_PATTERN = re.compile(r"uses:\s*([^@]+)@([a-f0-9]{7,40})")


def extract_uses(path: Path) -> List[Tuple[str, str]]:
    entries: List[Tuple[str, str]] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        match = USE_PATTERN.search(line)
        if match:
            entries.append((match.group(1).strip(), match.group(2).strip()))
    return entries


def generate_lock(root: Path) -> Dict[str, Dict[str, str]]:
    workflows_dir = root / ".github" / "workflows"
    lock: Dict[str, Dict[str, str]] = {}
    for workflow in sorted(workflows_dir.glob("*.yml")):
        uses = extract_uses(workflow)
        if uses:
            lock[str(workflow.relative_to(root))] = {name: sha for name, sha in uses}
    return lock


def main() -> int:
    root = Path.cwd()
    lock = generate_lock(root)
    json.dump({"workflows": lock}, sys.stdout, separators=(",", ":"), sort_keys=True)
    return 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
