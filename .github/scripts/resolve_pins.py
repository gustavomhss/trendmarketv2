#!/usr/bin/env python3
"""Resolve GitHub Action refs to immutable SHAs and update lock files."""

from __future__ import annotations

import json
import os
import re
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Sequence, Tuple
from urllib.request import Request, urlopen

FALLBACKS: Dict[str, str] = {
    "actions/checkout": "v4.2.2",
    "actions/upload-artifact": "v4",
    "actions/download-artifact": "v4",
    "actions/setup-python": "v5.3.0",
    "actions/cache": "v4",
    "actions/github-script": "v7",
}

PAT_INLINE = re.compile(
    r"^\s*(?:-\s*)?uses:\s*([\"\']?)([\w_.-]+\/[\w_.-]+)@([^\"\'\s#]+)\1\s*$"
)
PAT_KEY = re.compile(r"^\s*(?:-\s*)?uses:\s*$")
PAT_VALUE = re.compile(r"^\s*([\"\']?)([\w_.-]+\/[\w_.-]+)@([^\"\'\s#]+)\1\s*$")

ReportEntry = Tuple[str, str, str, str, str]


def _iter(obj: object | Sequence[object]) -> Iterable[object]:
    if obj is None:
        return []
    if isinstance(obj, Sequence) and not isinstance(obj, (str, bytes, bytearray)):
        return obj
    return [obj]


def _gh(url: str, token: Optional[str]) -> Optional[object]:
    headers = {"User-Agent": "pin-sweep"}
    if token:
        headers["Authorization"] = f"Bearer {token}"
    try:
        with urlopen(Request(url, headers=headers)) as response:
            return json.load(response)
    except Exception:
        return None


def resolve(owner_repo: str, ref: str, token: Optional[str]) -> Optional[str]:
    if re.fullmatch(r"[0-9a-fA-F]{40}", ref):
        return ref

    commit = _gh(f"https://api.github.com/repos/{owner_repo}/commits/{ref}", token)
    if isinstance(commit, dict):
        sha = commit.get("sha")
        if isinstance(sha, str):
            return sha

    tag_refs = _gh(f"https://api.github.com/repos/{owner_repo}/git/refs/tags/{ref}", token)
    for entry in _iter(tag_refs):
        if not isinstance(entry, dict):
            continue
        obj = entry.get("object")
        if not isinstance(obj, dict):
            continue
        sha = obj.get("sha")
        entry_type = obj.get("type")
        if not isinstance(sha, str):
            continue
        if entry_type == "tag":
            tag = _gh(f"https://api.github.com/repos/{owner_repo}/git/tags/{sha}", token)
            if isinstance(tag, dict):
                peeled = tag.get("object", {}).get("sha") if isinstance(tag.get("object"), dict) else None
                if isinstance(peeled, str):
                    return peeled
        return sha

    head_refs = _gh(f"https://api.github.com/repos/{owner_repo}/git/refs/heads/{ref}", token)
    for entry in _iter(head_refs):
        if not isinstance(entry, dict):
            continue
        obj = entry.get("object")
        if isinstance(obj, dict):
            sha = obj.get("sha")
            if isinstance(sha, str):
                return sha

    fallback = FALLBACKS.get(owner_repo)
    if fallback and fallback != ref:
        return resolve(owner_repo, fallback, token)
    return None


def _should_skip(action: str) -> bool:
    return action.startswith("./") or action.startswith("docker://")


def _replace_ref(line: str, sha: str) -> str:
    return re.sub(r"@[^\"'\s#]+", f"@{sha}", line)


def _record(
    entries: List[ReportEntry],
    kind: str,
    action: str,
    ref: str,
    sha: Optional[str],
    path: Path,
) -> None:
    entries.append((kind, action, ref, sha or "", str(path)))


def _process_reference(action: str, ref: str, token: Optional[str], path: Path, line: str, report: List[ReportEntry]) -> Tuple[str, bool]:
    if _should_skip(action):
        return line, False

    sha = resolve(action, ref, token)
    if sha and sha != ref:
        _record(report, "PIN", action, ref, sha, path)
        return _replace_ref(line, sha), True
    if sha:
        _record(report, "OK", action, ref, None, path)
        return line, False

    _record(report, "FAIL", action, ref, None, path)
    return line, False


def _process_file(path: Path, token: Optional[str]) -> Tuple[bool, List[ReportEntry]]:
    lines = path.read_text(encoding="utf-8", errors="ignore").splitlines(keepends=True)
    report: List[ReportEntry] = []
    output: List[str] = []
    changed = False
    index = 0

    while index < len(lines):
        line = lines[index]
        match = PAT_INLINE.match(line)
        if match:
            _, action, ref = match.groups()
            line, did_change = _process_reference(action, ref, token, path, line, report)
            changed = changed or did_change
            output.append(line)
            index += 1
            continue

        if PAT_KEY.match(line) and index + 1 < len(lines):
            next_line = lines[index + 1]
            value_match = PAT_VALUE.match(next_line)
            if value_match:
                _, action, ref = value_match.groups()
                new_line, did_change = _process_reference(action, ref, token, path, next_line, report)
                changed = changed or did_change
                output.append(line)
                output.append(new_line)
                index += 2
                continue

        output.append(line)
        index += 1

    if changed:
        path.write_text("".join(output), encoding="utf-8")

    return changed, report


def _collect_workflow_files() -> List[Path]:
    files: List[Path] = []
    root = Path(".github")
    if not root.exists():
        return files
    for path in root.rglob("*.yml"):
        files.append(path)
    for path in root.rglob("*.yaml"):
        files.append(path)
    files.sort()
    return files


def _write_reports(report: List[ReportEntry]) -> None:
    mapping: Dict[str, str] = {}
    for kind, action, ref, sha, _ in report:
        if kind in {"PIN", "OK"}:
            mapping[action] = sha or ref

    Path(".pins.report").write_text(
        "\n".join("\t".join(entry) for entry in report),
        encoding="utf-8",
    )
    lock_lines = ["actions:"]
    for action, ref in sorted(mapping.items()):
        lock_lines.append(f"  {action}: {ref}")
    lock_lines.append("metadata:")
    lock_lines.append("  updated_at: ")
    Path("actions.lock").write_text("\n".join(lock_lines), encoding="utf-8")


def main() -> int:
    token = os.environ.get("GITHUB_TOKEN") or os.environ.get("GH_TOKEN")
    report: List[ReportEntry] = []
    for path in _collect_workflow_files():
        _, entries = _process_file(path, token)
        report.extend(entries)
    if report:
        _write_reports(report)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
