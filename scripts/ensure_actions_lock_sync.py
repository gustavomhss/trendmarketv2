#!/usr/bin/env python3
"""Ensures actions.lock matches the SHAs used in workflow files."""

from __future__ import annotations

import os
import re
import sys
from dataclasses import dataclass
from typing import Dict, Iterable

INLINE_RE = re.compile(
    r'^\s*(?:-\s*)?uses:\s*(["\']?)([\w_.-]+/[\w_.-]+)@([^"\'\s#]+)\1\s*$'
)
KEY_RE = re.compile(r"^\s*(?:-\s*)?uses:\s*$")
VALUE_RE = re.compile(r'^\s*(["\']?)([\w_.-]+/[\w_.-]+)@([^"\'\s#]+)\1\s*$')
SHA_RE = re.compile(r"^[0-9a-fA-F]{40}$")


@dataclass
class Occurrence:
    file: str
    line: int
    action: str
    sha: str


def iter_yaml_files(base_dir: str = ".github") -> Iterable[str]:
    for root, _, files in os.walk(base_dir):
        for filename in files:
            if filename.endswith((".yml", ".yaml")):
                yield os.path.join(root, filename)


def extract_occurrences(path: str) -> Iterable[Occurrence]:
    with open(path, "r", encoding="utf-8", errors="ignore") as handle:
        lines = handle.read().splitlines()
    idx = 0
    while idx < len(lines):
        line = lines[idx]
        line_clean = line.split("#", 1)[0]
        match_inline = INLINE_RE.match(line_clean)
        if match_inline:
            _, action, ref = match_inline.groups()
            if not (action.startswith("./") or action.startswith("docker://")):
                yield Occurrence(path, idx + 1, action, ref)
            idx += 1
            continue
        if KEY_RE.match(line_clean) and idx + 1 < len(lines):
            next_line = lines[idx + 1]
            next_line_clean = next_line.split("#", 1)[0]
            match_value = VALUE_RE.match(next_line_clean)
            if match_value:
                _, action, ref = match_value.groups()
                if not (action.startswith("./") or action.startswith("docker://")):
                    yield Occurrence(path, idx + 2, action, ref)
                idx += 2
                continue
        idx += 1


def collect_actions() -> Dict[str, str]:
    mapping: Dict[str, str] = {}
    for file in iter_yaml_files():
        for occ in extract_occurrences(file):
            if not SHA_RE.fullmatch(occ.sha):
                continue
            current = mapping.get(occ.action)
            if current and current != occ.sha:
                raise SystemExit(
                    f"Action {occ.action} usa múltiplos SHAs: {current} e {occ.sha} (arquivo {occ.file})."
                )
            mapping[occ.action] = occ.sha
    return mapping


def load_actions_lock(path: str = "actions.lock") -> Dict[str, str]:
    actions: Dict[str, str] = {}
    if not os.path.exists(path):
        raise SystemExit("actions.lock inexistente.")
    section = None
    with open(path, "r", encoding="utf-8") as handle:
        for raw_line in handle:
            line = raw_line.split("#", 1)[0].rstrip()
            if not line:
                continue
            if line.strip() == "actions:":
                section = "actions"
                continue
            if line.strip() == "metadata:":
                section = None
                break
            if section == "actions" and ":" in line:
                key, value = line.split(":", 1)
                actions[key.strip()] = value.strip()
    return actions


def emit_summary(summary_path: str | None, lines: list[str]) -> None:
    if not summary_path:
        return
    with open(summary_path, "a", encoding="utf-8") as handle:
        handle.write("\n".join(lines) + "\n")


def main() -> int:
    workflow_actions = collect_actions()
    lock_actions = load_actions_lock()

    missing = sorted(set(workflow_actions) - set(lock_actions))
    extra = sorted(set(lock_actions) - set(workflow_actions))
    mismatched = sorted(
        action
        for action in set(workflow_actions) & set(lock_actions)
        if workflow_actions[action] != lock_actions[action]
    )

    summary = [
        "### Sync — actions.lock",
        "",
        f"* Actions detectadas nos workflows: {len(workflow_actions)}",
        f"* Actions presentes no lock: {len(lock_actions)}",
        "",
    ]

    status = 0
    if missing or extra or mismatched:
        status = 1
        if missing:
            summary.append("**Faltando no actions.lock:**")
            summary.extend(f"- {name}" for name in missing)
        if extra:
            summary.append("**Sobras no actions.lock:**")
            summary.extend(f"- {name}" for name in extra)
        if mismatched:
            summary.append("**SHA divergente:**")
            summary.extend(
                f"- {action}: workflow={workflow_actions[action]} lock={lock_actions[action]}"
                for action in mismatched
            )
    else:
        summary.append("Mapeamento em sincronia com actions.lock.")

    emit_summary(os.getenv("GITHUB_STEP_SUMMARY"), summary)

    if status != 0:
        print("actions.lock fora de sincronia.")
        if missing:
            print("Faltando:")
            for item in missing:
                print(f"  - {item}")
        if extra:
            print("Sobras:")
            for item in extra:
                print(f"  - {item}")
        if mismatched:
            print("Divergências:")
            for item in mismatched:
                print(
                    f"  - {item}: workflow={workflow_actions[item]} lock={lock_actions[item]}"
                )
    else:
        print("actions.lock sincronizado com workflows.")

    return status


if __name__ == "__main__":
    sys.exit(main())
