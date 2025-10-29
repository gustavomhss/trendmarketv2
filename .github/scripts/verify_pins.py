#!/usr/bin/env python3
"""Validate that GitHub workflow steps use pinned action SHAs."""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
import urllib.error
import urllib.request
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, Iterable, List, Tuple

ROOT = Path(__file__).resolve().parents[2]
DEFAULT_REPORT_PATH = ROOT / "out" / "guard" / "s4" / "actions_pins_report.json"
USER_AGENT = "trendmarketv2-actions-pins"
HEX40_RE = re.compile(r"^[0-9a-fA-F]{40}$")
INLINE_RE = re.compile(
    r'^\s*(?:-\s*)?uses:\s*(["\']?)([\w_.-]+\/[\w_.-]+)@([^"\'\s#]+)\1\s*$'
)
KEY_RE = re.compile(r"^\s*(?:-\s*)?uses:\s*$")
VALUE_RE = re.compile(r'^\s*(["\']?)([\w_.-]+\/[\w_.-]+)@([^"\'\s#]+)\1\s*$')


@dataclass
class PinIssue:
    file: str
    line: int
    repo: str
    ref: str
    reason: str


def list_yaml_files(base_dir: Path) -> Iterable[Path]:
    for root, _, files in os.walk(base_dir):
        for filename in files:
            if filename.endswith((".yml", ".yaml")):
                yield Path(root) / filename


def extract_uses(path: Path) -> List[Tuple[str, str, int]]:
    entries: List[Tuple[str, str, int]] = []
    with path.open("r", encoding="utf-8", errors="ignore") as handle:
        lines = handle.read().splitlines()
    idx = 0
    while idx < len(lines):
        line = lines[idx]
        line_clean = line.split("#", 1)[0]
        match = INLINE_RE.match(line_clean)
        if match:
            _, repo, ref = match.groups()
            if not (repo.startswith("./") or repo.startswith("docker://")):
                entries.append((repo, ref, idx + 1))
            idx += 1
            continue
        if KEY_RE.match(line_clean) and idx + 1 < len(lines):
            next_line = lines[idx + 1]
            next_line_clean = next_line.split("#", 1)[0]
            match_val = VALUE_RE.match(next_line_clean)
            if match_val:
                _, repo, ref = match_val.groups()
                if not (repo.startswith("./") or repo.startswith("docker://")):
                    entries.append((repo, ref, idx + 2))
                idx += 2
                continue
        idx += 1
    return entries


def commit_exists(repo: str, sha: str, token: str | None) -> bool:
    url = f"https://api.github.com/repos/{repo}/git/commits/{sha}"
    request = urllib.request.Request(url)
    request.add_header("Accept", "application/vnd.github+json")
    request.add_header("User-Agent", USER_AGENT)
    if token:
        request.add_header("Authorization", f"Bearer {token}")
    try:
        with urllib.request.urlopen(request, timeout=30):
            return True
    except urllib.error.HTTPError as exc:  # pragma: no cover - network failure path
        if exc.code in {404, 422}:
            return False
        raise
    except urllib.error.URLError as exc:  # pragma: no cover - network failure path
        raise RuntimeError(f"network error contacting GitHub: {exc}") from exc


def parse_args(argv: List[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--report",
        type=Path,
        default=DEFAULT_REPORT_PATH,
        help="Path to write JSON report (default: out/guard/s4/actions_pins_report.json)",
    )
    parser.add_argument(
        "--base",
        type=Path,
        default=ROOT / ".github",
        help="Base directory to scan for workflows (default: .github)",
    )
    return parser.parse_args(argv)


def build_summary(summary_path: str, lines: List[str]) -> None:
    if not summary_path:
        return
    with open(summary_path, "a", encoding="utf-8") as handle:
        handle.write("\n".join(lines) + "\n")


def main(argv: List[str] | None = None) -> int:
    args = parse_args(argv)
    report_path = (
        args.report if args.report.is_absolute() else (ROOT / args.report)
    ).resolve()
    base_dir = args.base if args.base.is_absolute() else (ROOT / args.base)

    token = os.getenv("GH_TOKEN") or os.getenv("GITHUB_TOKEN")

    files = sorted(list(list_yaml_files(base_dir)))
    occurrences: List[Tuple[Path, str, str, int]] = []
    for file_path in files:
        for repo, ref, line in extract_uses(file_path):
            occurrences.append((file_path, repo, ref, line))

    issues: List[PinIssue] = []
    checked_status: Dict[Tuple[str, str], bool] = {}
    for file_path, repo, ref, line in occurrences:
        if not HEX40_RE.fullmatch(ref):
            issues.append(
                PinIssue(
                    file=str(file_path.relative_to(ROOT)),
                    line=line,
                    repo=repo,
                    ref=ref,
                    reason="reference is not a 40-character SHA",
                )
            )
            continue
        key = (repo, ref.lower())
        if key not in checked_status:
            try:
                checked_status[key] = commit_exists(repo, ref.lower(), token)
            except RuntimeError as exc:
                print(f"[verify-pins] error: {exc}", file=sys.stderr)
                return 2
        if not checked_status[key]:
            issues.append(
                PinIssue(
                    file=str(file_path.relative_to(ROOT)),
                    line=line,
                    repo=repo,
                    ref=ref,
                    reason="commit does not exist or is inaccessible",
                )
            )

    report = {
        "generated_at": os.environ.get("GITHUB_RUN_ID") or "local",
        "files": len(files),
        "references": len(occurrences),
        "checked_commits": len(checked_status),
        "issues": [issue.__dict__ for issue in issues],
        "ok": not issues,
    }
    report_path.parent.mkdir(parents=True, exist_ok=True)
    report_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(f"[verify-pins] report written to {report_path}")

    summary_lines = [
        "### Sanity — Actions Pins",
        "",
        f"* Arquivos analisados: {len(files)}",
        f"* Referências verificadas: {len(occurrences)}",
        f"* Commits consultados: {len(checked_status)}",
        "",
    ]
    if issues:
        summary_lines.append("**Problemas encontrados:**")
        for entry in issues[:20]:
            summary_lines.append(
                f"- `{entry.repo}@{entry.ref}` em `{entry.file}` (linha {entry.line}): {entry.reason}"
            )
        if len(issues) > 20:
            summary_lines.append(f"- ... (+{len(issues) - 20} ocorrências)")
    else:
        summary_lines.append("Tudo OK — todas as actions usam SHAs válidos.")

    build_summary(os.getenv("GITHUB_STEP_SUMMARY", ""), summary_lines)

    if issues:
        for entry in issues:
            print(json.dumps(entry.__dict__, ensure_ascii=False))
        return 1

    print("OK")
    return 0


if __name__ == "__main__":  # pragma: no cover
    sys.exit(main())
