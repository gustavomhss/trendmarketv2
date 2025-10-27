#!/usr/bin/env python3
"""Lightweight guard that ensures public actions are pinned to 40-char SHAs."""
from __future__ import annotations

import os
import re
import sys
from dataclasses import dataclass

INLINE_RE = re.compile(r'^\s*(?:-\s*)?uses:\s*(["\']?)([\w_.-]+/[\w_.-]+)@([^"\'\s#]+)\1\s*$')
KEY_RE = re.compile(r'^\s*(?:-\s*)?uses:\s*$')
VALUE_RE = re.compile(r'^\s*(["\']?)([\w_.-]+/[\w_.-]+)@([^"\'\s#]+)\1\s*$')
SHA_RE = re.compile(r"^[0-9a-fA-F]{40}$")


@dataclass
class Occurrence:
    file: str
    line: int
    action: str
    ref: str


def iter_yaml_files(base_dir: str = ".github"):
    for root, _, files in os.walk(base_dir):
        for filename in files:
            if filename.endswith((".yml", ".yaml")):
                yield os.path.join(root, filename)


def extract_uses(path: str):
    with open(path, "r", encoding="utf-8", errors="ignore") as handle:
        lines = handle.read().splitlines()
    idx = 0
    while idx < len(lines):
        line = lines[idx]
        line_clean = line.split('#', 1)[0]
        inline = INLINE_RE.match(line_clean)
        if inline:
            _, action, ref = inline.groups()
            if not (action.startswith("./") or action.startswith("docker://")):
                yield Occurrence(path, idx + 1, action, ref)
            idx += 1
            continue
        if KEY_RE.match(line_clean) and idx + 1 < len(lines):
            next_line = lines[idx + 1]
            next_line_clean = next_line.split('#', 1)[0]
            block = VALUE_RE.match(next_line_clean)
            if block:
                _, action, ref = block.groups()
                if not (action.startswith("./") or action.startswith("docker://")):
                    yield Occurrence(path, idx + 2, action, ref)
                idx += 2
                continue
        idx += 1


def main() -> int:
    occurrences = [occ for file in iter_yaml_files() for occ in extract_uses(file)]
    errors: list[str] = []

    for occ in occurrences:
        if not SHA_RE.fullmatch(occ.ref):
            errors.append(
                f"{occ.file}:{occ.line}: `{occ.action}@{occ.ref}` não está pinado em SHA(40)."
            )

    if errors:
        for line in errors:
            print(line)
        return 1

    print(f"OK — {len(occurrences)} referências estão pinadas em SHAs de 40 caracteres.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
