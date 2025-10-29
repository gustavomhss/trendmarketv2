#!/usr/bin/env python3
import re
from pathlib import Path

ROOTS = [Path(".github/workflows")]
PAT = re.compile(
    r"^(\s*(?:-\s*)?uses\s*:\s*[\w.-]+/[\w.-]+@[0-9a-fA-F]{40,})(\s+#.*)?\s*$"
)


def normalize_file(path: Path) -> bool:
    lines = path.read_text(encoding="utf-8", errors="ignore").splitlines()
    changed = False
    output_lines = []
    for line in lines:
        if m := PAT.match(line):
            output_lines.append(m.group(1))
            changed = True
        else:
            output_lines.append(line)
    if changed:
        path.write_text("\n".join(output_lines) + "\n", encoding="utf-8")
    return changed


def main() -> None:
    any_changed = False
    for root in ROOTS:
        for file in root.rglob("*.y*ml"):
            any_changed |= normalize_file(file)
    print("[normalize-uses] changed" if any_changed else "[normalize-uses] clean")


if __name__ == "__main__":
    main()
