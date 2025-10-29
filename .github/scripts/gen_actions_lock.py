#!/usr/bin/env python3
"""Generate actions.lock with validated GitHub Action pins."""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
import re
import subprocess
import sys
import urllib.error
import urllib.request
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, Iterable, List, Tuple

ROOT = Path(__file__).resolve().parents[2]
DEFAULT_WORKFLOWS_DIR = ROOT / ".github" / "workflows"
DEFAULT_OUTPUT_PATH = ROOT / "actions.lock"
DEFAULT_EVIDENCE_PATH = ROOT / "out" / "guard" / "s4" / "actions.lock.json"
HEX40_RE = re.compile(r"^[0-9a-fA-F]{40}$")
ACTION_PATTERN = re.compile(
    r"^(?P<owner>[A-Za-z0-9_.-]+)/(?P<repo>[A-Za-z0-9_.-]+)"
    r"(?P<path>(?:/[A-Za-z0-9_.\-/]+)?)@(?P<ref>[^\s@]+)$"
)
USER_AGENT = "trendmarketv2-actions-lock-generator"

try:  # Prefer PyYAML, fallback to bundled parser when unavailable
    import yaml  # type: ignore
except ModuleNotFoundError:  # pragma: no cover - fallback for minimal environments
    sys.path.append(str(ROOT))
    import yaml_fallback as yaml  # type: ignore


@dataclass
class ActionUsage:
    owner: str
    repo: str
    path: str
    ref: str
    workflows: List[str]

    @property
    def repo_key(self) -> str:
        return (
            f"{self.owner}/{self.repo}{self.path}"
            if self.path
            else f"{self.owner}/{self.repo}"
        )


class GitHubAPIError(RuntimeError):
    """Raised when the GitHub API request fails."""

    def __init__(self, status: int, message: str) -> None:
        super().__init__(message)
        self.status = status


def utc_now() -> dt.datetime:
    return dt.datetime.now(dt.timezone.utc).replace(microsecond=0)


def isoformat_utc(value: dt.datetime | None = None) -> str:
    value = value or utc_now()
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


def _ls_remote(url: str, pattern: str) -> Dict[str, str]:
    proc = subprocess.run(
        ["git", "ls-remote", url, pattern],
        capture_output=True,
        text=True,
        check=False,
    )
    if proc.returncode != 0:
        return {}
    entries: Dict[str, str] = {}
    for line in proc.stdout.splitlines():
        line = line.strip()
        if not line:
            continue
        try:
            sha, name = line.split("\t", 1)
        except ValueError:
            continue
        entries[name] = sha.lower()
    return entries


def _candidate_patterns(ref: str) -> List[str]:
    patterns = [ref]
    if not ref.startswith("refs/"):
        patterns.extend(
            [
                f"{ref}^{{}}",
                f"refs/tags/{ref}",
                f"refs/tags/{ref}^{{}}",
                f"refs/heads/{ref}",
            ]
        )
    elif not ref.endswith("^{}"):
        patterns.append(f"{ref}^{{}}")
    return patterns


def resolve_with_git(owner: str, repo: str, ref: str) -> str | None:
    url = f"https://github.com/{owner}/{repo}.git"
    for pattern in _candidate_patterns(ref):
        mapping = _ls_remote(url, pattern)
        if not mapping:
            continue
        for name, sha in mapping.items():
            if name.endswith("^{}"):
                return sha
        normalized = pattern[:-3] if pattern.endswith("^{}") else pattern
        for name, sha in mapping.items():
            if name == normalized or name.endswith(f"/{normalized}"):
                return sha
        return next(iter(mapping.values()))
    return None


def validate_commit(owner: str, repo: str, sha: str, token: str | None) -> bool:
    url = f"https://api.github.com/repos/{owner}/{repo}/git/commits/{sha}"
    try:
        gh_api(url, token)
    except GitHubAPIError as exc:
        if exc.status in {404, 422}:
            return False
        raise
    return True


def peel_to_commit(owner: str, repo: str, sha: str, token: str | None) -> str | None:
    current = sha
    seen: set[str] = set()
    while current and current not in seen:
        seen.add(current)
        if validate_commit(owner, repo, current, token):
            return current.lower()
        try:
            tag_data = gh_api(
                f"https://api.github.com/repos/{owner}/{repo}/git/tags/{current}",
                token,
            )
        except GitHubAPIError as exc:
            if exc.status in {404, 422}:
                return None
            raise
        next_sha = tag_data.get("object", {}).get("sha")
        if not isinstance(next_sha, str):
            return None
        current = next_sha
    return None


def resolve_reference(
    owner: str, repo: str, ref: str, token: str | None
) -> Tuple[str, str]:
    if HEX40_RE.fullmatch(ref):
        sha = ref.lower()
        if not validate_commit(owner, repo, sha, token):
            raise RuntimeError(f"{owner}/{repo}@{ref} is not a valid commit SHA")
        source = "sha"
    else:
        resolved = resolve_with_git(owner, repo, ref)
        if not resolved:
            raise RuntimeError(
                f"Unable to resolve {owner}/{repo}@{ref} via git ls-remote"
            )
        peeled = peel_to_commit(owner, repo, resolved, token)
        if not peeled:
            raise RuntimeError(
                f"Unable to peel {owner}/{repo}@{ref} to a commit (resolved {resolved})"
            )
        sha = peeled
        source = "ref"
    return sha, source


def collect_uses(workflows_dir: Path) -> Dict[Tuple[str, str, str, str], ActionUsage]:
    references: Dict[Tuple[str, str, str, str], ActionUsage] = {}
    workflow_paths = sorted(workflows_dir.glob("*.yml")) + sorted(
        workflows_dir.glob("*.yaml")
    )
    for workflow_path in workflow_paths:
        try:
            document = yaml.safe_load(workflow_path.read_text(encoding="utf-8")) or {}
        except Exception as exc:  # pragma: no cover - defensive parsing
            print(f"[gen-lock] warning: failed to parse {workflow_path}: {exc}")
            continue
        jobs = document.get("jobs")
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
                match = ACTION_PATTERN.match(uses_value)
                if not match:
                    continue
                owner = match.group("owner")
                repo = match.group("repo")
                path = match.group("path") or ""
                ref = match.group("ref")
                key = (owner, repo, path, ref)
                usage = references.get(key)
                if usage is None:
                    usage = ActionUsage(
                        owner=owner,
                        repo=repo,
                        path=path,
                        ref=ref,
                        workflows=[],
                    )
                    references[key] = usage
                rel_path = str(workflow_path.relative_to(ROOT))
                if rel_path not in usage.workflows:
                    usage.workflows.append(rel_path)
    for usage in references.values():
        usage.workflows.sort()
    return references


def compute_metadata_sha(actions: List[Dict[str, str]]) -> str:
    payload = json.dumps(actions, sort_keys=True).encode("utf-8")
    return hashlib.sha1(payload).hexdigest()


def build_actions_list(
    usages: Dict[Tuple[str, str, str, str], ActionUsage],
    *,
    author: str,
    rationale: str,
    token: str | None,
) -> List[Dict[str, str]]:
    actions: List[Dict[str, str]] = []
    timestamp = isoformat_utc()
    for key in sorted(usages, key=lambda item: (item[0], item[1], item[2], item[3])):
        usage = usages[key]
        sha, source = resolve_reference(usage.owner, usage.repo, usage.ref, token)
        repo_key = usage.repo_key
        print(f"[gen-lock] {repo_key}@{usage.ref} -> {sha} ({source})")
        actions.append(
            {
                "repo": repo_key,
                "ref": usage.ref,
                "sha": sha,
                "date": timestamp,
                "author": author,
                "rationale": rationale,
                "url": f"https://github.com/{usage.owner}/{usage.repo}/commit/{sha}",
            }
        )
    return actions


def write_outputs(
    lock_data: Dict[str, object],
    *,
    output_path: Path,
    evidence_path: Path,
) -> None:
    text = json.dumps(lock_data, indent=2) + "\n"
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(text, encoding="utf-8")
    evidence_path.parent.mkdir(parents=True, exist_ok=True)
    evidence_path.write_text(text, encoding="utf-8")
    print(f"[gen-lock] wrote {output_path}")
    if evidence_path != output_path:
        print(f"[gen-lock] evidence copy at {evidence_path}")


def parse_args(argv: List[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--workflows",
        type=Path,
        default=DEFAULT_WORKFLOWS_DIR,
        help="Directory containing workflow files (default: .github/workflows)",
    )
    parser.add_argument(
        "--out",
        type=Path,
        default=DEFAULT_OUTPUT_PATH,
        help="Destination path for actions.lock (default: actions.lock)",
    )
    parser.add_argument(
        "--evidence",
        type=Path,
        default=DEFAULT_EVIDENCE_PATH,
        help="Path to write a copy for guard evidence (default: out/guard/s4/actions.lock.json)",
    )
    parser.add_argument(
        "--author",
        type=str,
        default="CI Bot <ci@trendmarketv2.local>",
        help="Author recorded in the lock metadata",
    )
    parser.add_argument(
        "--rationale",
        type=str,
        default="auto-sync action pins for workflow consistency",
        help="Rationale recorded in the lock metadata",
    )
    return parser.parse_args(argv)


def main(argv: List[str] | None = None) -> int:
    args = parse_args(argv)
    workflows_dir = (
        (ROOT / args.workflows).resolve()
        if not args.workflows.is_absolute()
        else args.workflows
    )
    output_path = (
        (ROOT / args.out).resolve() if not args.out.is_absolute() else args.out
    )
    evidence_path = (
        (ROOT / args.evidence).resolve()
        if not args.evidence.is_absolute()
        else args.evidence
    )

    usages = collect_uses(workflows_dir)
    if not usages:
        print("[gen-lock] no GitHub actions detected", file=sys.stderr)
        return 1

    token = os.getenv("GITHUB_TOKEN") or os.getenv("GH_TOKEN")
    try:
        actions = build_actions_list(
            usages, author=args.author, rationale=args.rationale, token=token
        )
    except RuntimeError as exc:
        print(f"[gen-lock] error: {exc}", file=sys.stderr)
        return 2

    metadata = {
        "sha": "",
        "date": isoformat_utc(),
        "author": args.author,
        "rationale": args.rationale,
    }
    lock_data = {"version": 1, "metadata": metadata, "actions": actions}
    metadata["sha"] = compute_metadata_sha(actions)

    write_outputs(lock_data, output_path=output_path, evidence_path=evidence_path)
    return 0


if __name__ == "__main__":  # pragma: no cover
    sys.exit(main())
