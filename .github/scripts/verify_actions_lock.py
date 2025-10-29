#!/usr/bin/env python3
"""Validate actions.lock structure and pinned GitHub actions."""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
import urllib.error
import urllib.request
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Iterable, List, Tuple

ROOT = Path(__file__).resolve().parents[2]
DEFAULT_LOCK_PATH = ROOT / "actions.lock"
DEFAULT_REPORT_PATH = ROOT / "out" / "guard" / "s4" / "actions_lock_report.json"
HEX40_RE = re.compile(r"^[0-9a-fA-F]{40}$")
ACTION_PATTERN = re.compile(
    r"^(?P<owner>[A-Za-z0-9_.-]+)/(?P<repo>[A-Za-z0-9_.-]+)(?P<path>(?:/[A-Za-z0-9_.\-/]+)?)$"
)
USER_AGENT = "trendmarketv2-actions-lock-verify"

try:  # Prefer PyYAML, fallback to bundled parser when unavailable
    import yaml  # type: ignore
except ModuleNotFoundError:  # pragma: no cover - fallback for minimal environments
    sys.path.append(str(ROOT))
    import yaml_fallback as yaml  # type: ignore


@dataclass
class ValidationIssue:
    scope: str
    message: str


class GitHubAPIError(RuntimeError):
    """Raised when the GitHub API request fails."""

    def __init__(self, status: int, message: str) -> None:
        super().__init__(message)
        self.status = status


def isoformat_utc(value: datetime | None = None) -> str:
    value = value or datetime.now(timezone.utc).replace(microsecond=0)
    return value.isoformat().replace("+00:00", "Z")


def gh_api(url: str, token: str | None) -> dict:
    request = urllib.request.Request(url)
    request.add_header("Accept", "application/vnd.github+json")
    request.add_header("User-Agent", USER_AGENT)
    if token:
        request.add_header("Authorization", f"Bearer {token}")
    try:
        with urllib.request.urlopen(request, timeout=30) as response:
            return json.loads(response.read().decode("utf-8"))
    except urllib.error.HTTPError as exc:  # pragma: no cover - network failure path
        message = exc.read().decode("utf-8", errors="ignore")
        raise GitHubAPIError(exc.code, message)
    except urllib.error.URLError as exc:  # pragma: no cover - network failure path
        raise GitHubAPIError(0, str(exc))


def validate_commit(
    owner: str, repo: str, sha: str, token: str | None
) -> Tuple[bool, str | None]:
    url = f"https://api.github.com/repos/{owner}/{repo}/git/commits/{sha}"
    try:
        payload = gh_api(url, token)
    except GitHubAPIError as exc:
        if exc.status in {404, 422}:
            return False, None
        raise
    tree_sha = payload.get("sha") if isinstance(payload, dict) else None
    return True, tree_sha


def parse_args(argv: List[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "lock_path",
        nargs="?",
        type=Path,
        default=DEFAULT_LOCK_PATH,
        help="Path to actions.lock (default: actions.lock)",
    )
    parser.add_argument(
        "--report",
        type=Path,
        default=DEFAULT_REPORT_PATH,
        help="Path to write JSON report (default: out/guard/s4/actions_lock_report.json)",
    )
    return parser.parse_args(argv)


def load_lock(path: Path) -> dict:
    try:
        text = path.read_text(encoding="utf-8")
    except OSError as exc:
        raise RuntimeError(f"unable to read {path}: {exc}") from exc
    try:
        return json.loads(text)
    except json.JSONDecodeError as exc:  # pragma: no cover - schema error path
        raise RuntimeError(f"invalid JSON in {path}: {exc}") from exc


def collect_workflow_uses(workflows_dir: Path) -> List[Tuple[str, str]]:
    results: List[Tuple[str, str]] = []
    workflow_paths = sorted(workflows_dir.glob("*.yml")) + sorted(
        workflows_dir.glob("*.yaml")
    )
    for workflow_path in workflow_paths:
        try:
            data = yaml.safe_load(workflow_path.read_text(encoding="utf-8")) or {}
        except Exception:  # pragma: no cover - defensive parsing
            continue
        jobs = data.get("jobs")
        if not isinstance(jobs, dict):
            continue
        for job in jobs.values():
            steps = (job or {}).get("steps")
            if not isinstance(steps, Iterable):
                continue
            for step in steps:
                if not isinstance(step, dict):
                    continue
                value = step.get("uses")
                if not value:
                    continue
                uses_value = str(value).strip()
                if uses_value.startswith("./") or uses_value.startswith("docker://"):
                    continue
                results.append((str(workflow_path.relative_to(ROOT)), uses_value))
    return results


def validate_lock_structure(lock: dict) -> List[ValidationIssue]:
    issues: List[ValidationIssue] = []
    if lock.get("version") != 1:
        issues.append(ValidationIssue("metadata", "version must equal 1"))

    metadata = lock.get("metadata")
    if not isinstance(metadata, dict):
        issues.append(ValidationIssue("metadata", "metadata must be an object"))
    else:
        for field in ("sha", "date", "author", "rationale"):
            value = metadata.get(field)
            if not isinstance(value, str) or not value.strip():
                issues.append(ValidationIssue("metadata", f"{field} missing or empty"))
        sha_value = metadata.get("sha")
        if isinstance(sha_value, str) and not HEX40_RE.fullmatch(sha_value):
            issues.append(
                ValidationIssue("metadata", "metadata.sha must be 40 hex characters")
            )
        date_value = metadata.get("date")
        if isinstance(date_value, str):
            try:
                datetime.fromisoformat(date_value.replace("Z", "+00:00"))
            except ValueError:
                issues.append(
                    ValidationIssue("metadata", "metadata.date is not ISO-8601")
                )

    actions = lock.get("actions")
    if not isinstance(actions, list) or not actions:
        issues.append(ValidationIssue("actions", "actions list missing or empty"))

    return issues


def validate_actions_entries(
    actions: List[dict],
    token: str | None,
) -> Tuple[List[ValidationIssue], int]:
    issues: List[ValidationIssue] = []
    checked = 0
    for entry in actions:
        if not isinstance(entry, dict):
            issues.append(ValidationIssue("actions", "entry must be an object"))
            continue
        repo_value = entry.get("repo")
        ref_value = entry.get("ref")
        sha_value = entry.get("sha")
        date_value = entry.get("date")
        author_value = entry.get("author")
        rationale_value = entry.get("rationale")
        url_value = entry.get("url")
        identifier = (
            f"{repo_value}@{ref_value}" if repo_value and ref_value else str(repo_value)
        )
        for field_name, value in (
            ("repo", repo_value),
            ("ref", ref_value),
            ("sha", sha_value),
            ("date", date_value),
            ("author", author_value),
            ("rationale", rationale_value),
            ("url", url_value),
        ):
            if not isinstance(value, str) or not value.strip():
                issues.append(
                    ValidationIssue(identifier, f"field {field_name} missing")
                )
        if not isinstance(sha_value, str) or not HEX40_RE.fullmatch(sha_value):
            issues.append(ValidationIssue(identifier, "sha must be a 40-character hex"))
            continue
        if not isinstance(repo_value, str) or not ACTION_PATTERN.match(repo_value):
            issues.append(
                ValidationIssue(identifier, "repo must follow owner/repo[/path]")
            )
            continue
        owner, repo, _ = ACTION_PATTERN.match(repo_value).groups()  # type: ignore[arg-type]
        try:
            valid, _ = validate_commit(owner, repo, sha_value.lower(), token)
        except GitHubAPIError as exc:
            issues.append(
                ValidationIssue(
                    identifier,
                    f"failed to validate commit via API (status {exc.status})",
                )
            )
            continue
        if not valid:
            issues.append(
                ValidationIssue(identifier, "commit does not exist or is inaccessible")
            )
        checked += 1
    return issues, checked


def validate_workflow_pins(workflows_dir: Path) -> List[ValidationIssue]:
    issues: List[ValidationIssue] = []
    for workflow, uses_value in collect_workflow_uses(workflows_dir):
        if "@" not in uses_value:
            issues.append(
                ValidationIssue(workflow, f"uses entry without @: {uses_value}")
            )
            continue
        ref = uses_value.split("@", 1)[1].strip()
        if not HEX40_RE.fullmatch(ref):
            issues.append(
                ValidationIssue(workflow, f"reference not pinned to SHA: {uses_value}")
            )
    return issues


def main(argv: List[str] | None = None) -> int:
    args = parse_args(argv)
    lock_path = (
        args.lock_path if args.lock_path.is_absolute() else (ROOT / args.lock_path)
    ).resolve()
    report_path = (
        args.report if args.report.is_absolute() else (ROOT / args.report)
    ).resolve()

    try:
        lock_data = load_lock(lock_path)
    except RuntimeError as exc:
        print(f"[verify-lock] error: {exc}", file=sys.stderr)
        return 2

    token = os.getenv("GITHUB_TOKEN") or os.getenv("GH_TOKEN")

    issues = validate_lock_structure(lock_data)
    actions = lock_data.get("actions")
    checked_actions = 0
    if isinstance(actions, list) and actions:
        action_issues, checked_actions = validate_actions_entries(actions, token)
        issues.extend(action_issues)
    workflows_dir = ROOT / ".github" / "workflows"
    issues.extend(validate_workflow_pins(workflows_dir))

    report = {
        "lock_path": str(lock_path.relative_to(ROOT)),
        "checked_actions": checked_actions,
        "issues": [
            {"scope": issue.scope, "message": issue.message} for issue in issues
        ],
        "ok": not issues,
        "generated_at": isoformat_utc(),
    }
    report_path.parent.mkdir(parents=True, exist_ok=True)
    report_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(f"[verify-lock] report written to {report_path}")

    if issues:
        for issue in issues:
            print(f"[verify-lock] {issue.scope}: {issue.message}", file=sys.stderr)
        return 1
    print("[verify-lock] actions.lock validated successfully")
    return 0


if __name__ == "__main__":  # pragma: no cover
    sys.exit(main())
