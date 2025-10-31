#!/usr/bin/env python3
"""Pin selected GitHub Actions to specific commit SHAs."""
from __future__ import annotations

import re
from pathlib import Path

PIN_MAP = {
    "actions/checkout": "11bd71901bbe5b1630ceea73d27597364c9af683",
    "actions/upload-artifact": "ea165f8d65b6e75b540449e92b4886f43607fa02",
    "actions/download-artifact": "d3f86a106a0bac45b974a628896c90dbdf5c8093",
    "actions/setup-python": "42375524e23c412d93fb67b49958b491fce71c38",
}

SHA_RE = re.compile(r"^[0-9a-f]{30,}$")
USES_RE = re.compile(r"^(?P<prefix>\s*uses:\s*)(?P<repo>[^@\s]+)@(?P<ref>[^\s]+)(?P<suffix>.*)$")


def should_skip(repo: str) -> bool:
    return repo.startswith("./") or repo.startswith("docker://")


def pin_line(line: str) -> tuple[str, bool]:
    match = USES_RE.match(line)
    if not match:
        return line, False

    repo = match.group("repo")
    if should_skip(repo):
        return line, False

    pin = PIN_MAP.get(repo)
    if not pin:
        return line, False

    current_ref = match.group("ref")
    if SHA_RE.fullmatch(current_ref):
        return line, False

    new_line = f"{match.group('prefix')}{repo}@{pin}{match.group('suffix')}"
    return new_line, True


def iter_workflow_files() -> list[Path]:
    base = Path(".github/workflows")
    if not base.exists():
        return []
    files = []
    for pattern in ("*.yml", "*.yaml"):
        files.extend(base.rglob(pattern))
    return sorted({f for f in files if f.is_file()})


def main() -> None:
    changed_files: list[Path] = []
    for wf in iter_workflow_files():
        original = wf.read_text(encoding="utf-8")
        lines = original.splitlines(keepends=True)
        modified = False
        new_lines = []
        for line in lines:
            new_line, changed = pin_line(line)
            if changed:
                modified = True
            new_lines.append(new_line)
        if modified:
            new_content = "".join(new_lines)
            wf.write_text(new_content, encoding="utf-8")
            changed_files.append(wf)
    if changed_files:
        for wf in changed_files:
            print(f"[pin] updated {wf}")
    else:
        print("[pin] no changes needed")


if __name__ == "__main__":
    main()
