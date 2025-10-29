#!/usr/bin/env python3
"""Utility to pin GitHub Actions references in workflow files."""

from __future__ import annotations

import argparse
import pathlib
import re
from typing import Iterable

PIN_MAP = {
    "actions/checkout@v4": "actions/checkout@11bd71901bbe5b1630ceea73d27597364c9af683",
    "actions/upload-artifact@v4": "actions/upload-artifact@ea165f8d65b6e75b540449e92b4886f43607fa02",
    "actions/download-artifact@v4": "actions/download-artifact@cc20338ba2f079446182a90c0d65f173b7af4b23",
    "actions/setup-python@v5": "actions/setup-python@42375524e23c412d93fb67b49958b491fce71c38",
    "docker/login-action@v3": "docker/login-action@5e57cd118135c172c3672efd75eb46360885c0ef",
}

USES_RE = re.compile(
    r"^(?P<prefix>\s*(?:-\s*)?uses:\s*)(?P<quote>[\"\']?)(?P<ref>[^\s\"\'#]+)(?P=quote)(?P<suffix>.*)$"
)


def iter_workflow_files(paths: Iterable[pathlib.Path]) -> Iterable[pathlib.Path]:
    for root in paths:
        if root.is_file() and root.suffix in {".yml", ".yaml"}:
            yield root
        elif root.is_dir():
            yield from (path for path in root.rglob("*.yml"))
            yield from (path for path in root.rglob("*.yaml"))


def rewrite_line(line: str) -> tuple[str, bool]:
    ending = ""
    if line.endswith("\r\n"):
        ending = "\r\n"
        body = line[:-2]
    elif line.endswith("\n"):
        ending = "\n"
        body = line[:-1]
    else:
        body = line

    match = USES_RE.match(body)
    if not match:
        return line, False

    ref = match.group("ref")
    pinned = PIN_MAP.get(ref)
    if not pinned:
        return line, False

    comment = f"  # pinned (was {ref.split('@', 1)[1]})"

    replacement = (
        f"{match.group('prefix')}{match.group('quote')}{pinned}{match.group('quote')}"
    )
    suffix = match.group("suffix") or ""
    if suffix.strip():
        replacement += suffix
    replacement += comment

    return replacement + ending, True


def apply_pin(path: pathlib.Path) -> int:
    original = path.read_text(encoding="utf-8")
    lines = original.splitlines(keepends=True)
    changed = 0
    new_lines = []
    for line in lines:
        new_line, updated = rewrite_line(line)
        new_lines.append(new_line)
        if updated:
            changed += 1
    if changed:
        path.write_text("".join(new_lines), encoding="utf-8")
    return changed


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "paths",
        nargs="*",
        type=pathlib.Path,
        default=[pathlib.Path(".github/workflows")],
        help="Workflow directories or files to rewrite.",
    )
    args = parser.parse_args()

    changed_files = 0
    changed_lines = 0
    for file_path in iter_workflow_files(args.paths):
        delta = apply_pin(file_path)
        if delta:
            changed_files += 1
            changed_lines += delta
    print(f"[pin] changed_files={changed_files} changed_lines={changed_lines}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
