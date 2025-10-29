#!/usr/bin/env python3
import re
from pathlib import Path

ROOTS = [Path(".")]
SKIP = re.compile(
    r"(^|/)(\.git|\.ruff_cache|\.venv|venv|node_modules|out|dist|build)(/|$)"
)
RGX = re.compile(r"^(\s*)import\s+([^#\n]+?)(\s*#.*)?\s*$")


def split_items(s):
    return [x.strip() for x in s.split(",") if x.strip()]


def rewrite(path: Path) -> bool:
    t = path.read_text(encoding="utf-8", errors="ignore").splitlines()
    out, changed = [], False
    for line in t:
        m = RGX.match(line)
        if m and "," in m.group(2):
            indent, items, cmt = m.group(1), m.group(2), (m.group(3) or "")
            names = split_items(items)
            for name in names:
                out.append(f"{indent}import {name}{cmt}")
                cmt = ""  # comentário só na primeira linha
            changed = True
        else:
            out.append(line)
    if changed:
        Path(path).write_text("\n".join(out) + "\n", encoding="utf-8")
    return changed


def main():
    any_changed = False
    for root in ROOTS:
        for p in root.rglob("*.py"):
            if SKIP.search(str(p)):
                continue
            try:
                if rewrite(p):
                    any_changed = True
            except Exception:
                pass
    print("[E401-fix] changed" if any_changed else "[E401-fix] clean")


if __name__ == "__main__":
    main()
