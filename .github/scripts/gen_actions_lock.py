#!/usr/bin/env python3
"""Generate a deterministic actions.lock file from workflow usages."""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Sequence, Set, Tuple
from urllib.error import HTTPError, URLError
from urllib.request import Request, urlopen

GITHUB_API = os.environ.get("GITHUB_API_URL", "https://api.github.com")
GITHUB_TOKEN = os.environ.get("GITHUB_TOKEN") or os.environ.get("GH_TOKEN")

USES_RE = re.compile(
    r"^(?P<owner>[A-Za-z0-9_.-]+)/(?P<repo>[A-Za-z0-9_.-]+)(?P<path>(?:/[A-Za-z0-9_.\-/]+)?)@(?P<ref>[^\s#]+)$"
)
HEX40_RE = re.compile(r"^[0-9a-fA-F]{40}$")
INLINE_RE = re.compile(
    r'^\s*(?:-\s*)?uses:\s*(["\']?)([\w./-]+/[\w./-]+@[^"\'\s#]+)\1\s*$'
)
KEY_RE = re.compile(r"^\s*(?:-\s*)?uses:\s*$")
VALUE_RE = re.compile(r'^\s*(["\']?)([\w./-]+/[\w./-]+@[^"\'\s#]+)\1\s*$')
ACTION_RATIONALE = "auto-sync action pins for workflow consistency"
DEFAULT_CI_AUTHOR = "CI Bot <ci@trendmarketv2.local>"


class LockError(Exception):
    """Raised when lock generation fails."""


def run(cmd: Sequence[str]) -> str:
    return subprocess.check_output(cmd, text=True).strip()


def git_head_sha() -> str:
    try:
        return run(["git", "rev-parse", "HEAD"]).strip()[:40]
    except Exception:
        return f"{int(time.time()):040x}"[:40]


def isoformat_now() -> str:
    return (
        datetime.now(timezone.utc)
        .replace(microsecond=0)
        .isoformat()
        .replace("+00:00", "Z")
    )


def http_get(url: str) -> dict:
    headers = {"Accept": "application/vnd.github+json"}
    if GITHUB_TOKEN:
        headers["Authorization"] = f"Bearer {GITHUB_TOKEN}"
    request = Request(url, headers=headers)
    try:
        with urlopen(request, timeout=30) as response:
            charset = response.headers.get_content_charset() or "utf-8"
            payload = response.read().decode(charset)
            return json.loads(payload)
    except HTTPError as exc:
        if exc.code == 404:
            raise LockError(f"Resource not found: {url}") from exc
        raise LockError(f"HTTP error {exc.code} for {url}") from exc
    except URLError as exc:  # pragma: no cover - network failure
        raise LockError(f"Network error for {url}: {exc}") from exc


def resolve_commit(owner: str, repo: str, ref: str) -> Tuple[str, str, str]:
    meta = http_get(f"{GITHUB_API}/repos/{owner}/{repo}/commits/{ref}")
    sha = ref.lower() if HEX40_RE.fullmatch(ref) else str(meta.get("sha", "")).lower()
    if not HEX40_RE.fullmatch(sha):
        raise LockError(f"Invalid SHA for {owner}/{repo}@{ref}: {sha}")
    commit_info = meta.get("commit", {})
    author_info = commit_info.get("author") or {}
    committer_info = commit_info.get("committer") or {}
    author = author_info.get("name") or committer_info.get("name") or "Unknown"
    date_raw = author_info.get("date") or committer_info.get("date") or isoformat_now()
    try:
        dt = datetime.fromisoformat(date_raw.replace("Z", "+00:00")).astimezone(
            timezone.utc
        )
        date = dt.replace(microsecond=0).isoformat().replace("+00:00", "Z")
    except Exception:
        date = isoformat_now()
    return sha, author, date


def commit_url(repo: str, sha: str) -> str:
    parts = repo.split("/", 2)
    if len(parts) >= 2:
        return f"https://github.com/{parts[0]}/{parts[1]}/commit/{sha}"
    return ""


def build_entry(
    repo: str,
    ref: str,
    sha: str,
    date: str,
    author: str,
    rationale: str,
    url: Optional[str] = None,
) -> Dict[str, str]:
    sha = sha.lower()
    return {
        "repo": repo,
        "ref": ref,
        "sha": sha,
        "date": date,
        "author": author.strip() or DEFAULT_CI_AUTHOR,
        "rationale": rationale.strip() or ACTION_RATIONALE,
        "url": url or commit_url(repo, sha),
    }


def iter_workflow_files(directory: Path) -> Iterable[Path]:
    for path in sorted(directory.rglob("*.yml")):
        yield path
    for path in sorted(directory.rglob("*.yaml")):
        if path.suffix != ".yml":
            yield path


def extract_uses_from_text(text: str) -> Set[str]:
    results: Set[str] = set()
    lines = text.splitlines()
    idx = 0
    while idx < len(lines):
        line = lines[idx]
        line_clean = line.split("#", 1)[0]
        match_inline = INLINE_RE.match(line_clean)
        if match_inline:
            results.add(match_inline.group(2).strip())
            idx += 1
            continue
        if KEY_RE.match(line_clean) and idx + 1 < len(lines):
            next_line = lines[idx + 1]
            next_clean = next_line.split("#", 1)[0]
            match_value = VALUE_RE.match(next_clean)
            if match_value:
                results.add(match_value.group(2).strip())
                idx += 2
                continue
        idx += 1
    return results


def parse_workflows(directory: Path) -> Set[str]:
    seen: Set[str] = set()
    for workflow in iter_workflow_files(directory):
        try:
            content = workflow.read_text(encoding="utf-8")
        except OSError as exc:
            print(f"[warn] Failed to read {workflow}: {exc}")
            continue
        seen |= extract_uses_from_text(content)
    return seen


def filter_action_refs(uses_items: Iterable[str]) -> List[Tuple[str, str, str, str]]:
    refs: List[Tuple[str, str, str, str]] = []
    for entry in sorted(set(uses_items)):
        if (
            entry.startswith("./")
            or entry.startswith(".\\")
            or entry.startswith("docker://")
        ):
            continue
        match = USES_RE.match(entry)
        if not match:
            continue
        owner = match.group("owner")
        repo = match.group("repo")
        path = match.group("path") or ""
        ref = match.group("ref")
        refs.append((owner, repo, path, ref))
    return refs


def build_lock(
    actions: List[Dict[str, str]], author: str, rationale: str
) -> Dict[str, object]:
    canonical_author = author.strip() or DEFAULT_CI_AUTHOR
    canonical_rationale = rationale.strip() or ACTION_RATIONALE
    metadata = {
        "sha": git_head_sha(),
        "date": isoformat_now(),
        "author": canonical_author,
        "rationale": canonical_rationale,
    }
    return {
        "version": 1,
        "metadata": metadata,
        "actions": actions,
    }


def load_cached_actions(path: Path) -> Dict[Tuple[str, str], Dict[str, str]]:
    candidates = [path]
    alt = Path(".github/actions.lock")
    if alt != path and alt.exists():
        candidates.append(alt)
    cached: Dict[Tuple[str, str], Dict[str, str]] = {}
    for candidate in candidates:
        if not candidate.exists():
            continue
        try:
            data = json.loads(candidate.read_text(encoding="utf-8"))
        except Exception:
            continue
        actions = data.get("actions") if isinstance(data, dict) else None
        metadata = data.get("metadata") if isinstance(data, dict) else {}
        meta_author = "Unknown"
        meta_date = isoformat_now()
        if isinstance(metadata, dict):
            meta_author = str(
                metadata.get("author") or metadata.get("updated_by") or meta_author
            ).strip()
            if not meta_author or meta_author.lower() == "ci/boss-final":
                meta_author = DEFAULT_CI_AUTHOR
            meta_date = str(
                metadata.get("date") or metadata.get("updated_at") or meta_date
            )
        if isinstance(actions, list):
            for entry in actions:
                if not isinstance(entry, dict):
                    continue
                repo = entry.get("repo") or entry.get("uses")
                ref = entry.get("ref") or entry.get("sha")
                sha = entry.get("sha")
                date = entry.get("date") or meta_date
                author_raw = entry.get("author") or meta_author
                author = (
                    DEFAULT_CI_AUTHOR
                    if str(author_raw).strip().lower() == "ci/boss-final"
                    else str(author_raw or "").strip()
                )
                rationale = entry.get("rationale") or ACTION_RATIONALE
                url = entry.get("url")
                if (
                    not isinstance(repo, str)
                    or not isinstance(ref, str)
                    or not isinstance(sha, str)
                ):
                    continue
                cached[(repo, ref)] = build_entry(
                    repo, ref, sha, date, author, rationale, url
                )
        elif isinstance(actions, dict):
            for repo, sha in actions.items():
                if not isinstance(repo, str) or not isinstance(sha, str):
                    continue
                cached[(repo, sha)] = build_entry(
                    repo,
                    sha,
                    sha,
                    meta_date,
                    meta_author,
                    ACTION_RATIONALE,
                )
    return cached


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description="Generate actions.lock")
    parser.add_argument(
        "--workflows", default=".github/workflows", help="Workflow directory"
    )
    parser.add_argument("--out", default="actions.lock", help="Output file path")
    parser.add_argument(
        "--author",
        default=os.environ.get("GITHUB_ACTOR") or DEFAULT_CI_AUTHOR,
    )
    parser.add_argument("--rationale", default=ACTION_RATIONALE)
    args = parser.parse_args(argv)

    workflow_dir = Path(args.workflows)
    if not workflow_dir.exists():
        raise SystemExit(f"Workflows não encontrados: {workflow_dir}")

    uses_entries = parse_workflows(workflow_dir)
    refs = filter_action_refs(uses_entries)

    cached_entries = load_cached_actions(Path(args.out))
    lock_entries: List[Dict[str, str]] = []
    seen_keys: Set[Tuple[str, str]] = set()
    for owner, repo, path, ref in refs:
        key = (f"{owner}/{repo}{path}", ref)
        if key in seen_keys:
            continue
        seen_keys.add(key)
        action_id = f"{owner}/{repo}{path}"
        try:
            sha, commit_author, commit_date = resolve_commit(owner, repo, ref)
            entry = build_entry(
                action_id,
                ref,
                sha,
                commit_date,
                commit_author,
                ACTION_RATIONALE,
            )
            print(f"[lock] {action_id}@{ref} -> {sha}")
        except LockError as exc:
            cached_entry = cached_entries.get((action_id, ref))
            if not cached_entry:
                raise
            entry = dict(cached_entry)
            entry.update(
                {
                    "repo": action_id,
                    "ref": ref,
                    "rationale": ACTION_RATIONALE,
                }
            )
            entry["sha"] = str(entry.get("sha", "")).lower()
            if not entry.get("url") and entry.get("sha"):
                entry["url"] = commit_url(action_id, entry["sha"])
            print(f"[warn] {action_id}@{ref}: usando metadata em cache ({exc})")
        lock_entries.append(entry)

    lock_entries.sort(key=lambda item: (item["repo"].lower(), item["ref"].lower()))
    lock = build_lock(lock_entries, args.author, args.rationale)

    output_path = Path(args.out)
    output_path.write_text(
        json.dumps(lock, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )
    print(f"[ok] Escrito: {output_path} ({len(lock_entries)} actions)")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except LockError as exc:
        print(f"[error] {exc}")
        sys.exit(2)
