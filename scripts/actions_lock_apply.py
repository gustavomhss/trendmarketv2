#!/usr/bin/env python3
"""Pin GitHub Actions references to immutable commit SHAs."""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, Iterable, Iterator, List, Optional, Tuple
from urllib.error import HTTPError, URLError
from urllib.parse import quote, urlparse
from urllib.request import Request, urlopen


ISO_FORMAT = "%Y-%m-%dT%H:%M:%SZ"
LOCK_AUTHOR = "ci/boss-final"
LOCK_RATIONALE = (
    "Pin to immutable commit SHA for supply-chain safety and reproducibility"
)
METADATA_AUTHOR = "scripts/actions_lock_apply.py"
OUT_DIR = Path("out/s4-actions-lock")
LOCK_PATH = Path(".github/actions.lock")
METADATA_PATH = Path(".github/actions.metadata.json")
WORKFLOWS_DIR = Path(".github/workflows")


class ActionsLockError(Exception):
    """Base error for the actions lock flow."""


class ResolutionError(ActionsLockError):
    """Raised when an action reference cannot be resolved."""

    def __init__(self, message: str, *, transient: bool = False) -> None:
        super().__init__(message)
        self.transient = transient


class GitHubAPIError(ResolutionError):
    """Raised when the GitHub API cannot satisfy a request."""


class GitCLIError(ResolutionError):
    """Raised when the git CLI cannot satisfy a request."""


USES_REGEX = re.compile(r"^(?P<prefix>\s*(?:-\s+)?uses:\s*)(?P<rest>.*)$")
ACTION_REGEX = re.compile(
    r"^(?P<owner>[A-Za-z0-9_.-]+)/(?P<repo>[A-Za-z0-9_.-]+)"
    r"(?P<path>(?:/[A-Za-z0-9_.\-/]+)?)@(?P<ref>[^\s@]+)$"
)


def utc_now() -> datetime:
    return datetime.now(timezone.utc).replace(microsecond=0)


def format_datetime(value: datetime) -> str:
    return value.strftime(ISO_FORMAT)


def is_sha(value: str) -> bool:
    return bool(re.fullmatch(r"[0-9a-f]{40}", value))


def git_hash_object(data: bytes, *, cwd: Path) -> str:
    proc = subprocess.run(
        ["git", "hash-object", "--stdin"],
        input=data,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=True,
        cwd=cwd,
    )
    return proc.stdout.decode().strip()


def ensure_parent(path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)


@dataclass
class ActionReference:
    owner: str
    repo: str
    path: str
    ref: str

    @property
    def full_name(self) -> str:
        return f"{self.owner}/{self.repo}{self.path}"


@dataclass
class WorkflowUsage:
    workflow_path: Path
    line_index: int
    prefix: str
    quote: str
    value: str
    comment: str
    line_ending: str
    reference: ActionReference
    resolved_sha: Optional[str] = None

    def original_uses(self) -> str:
        return f"{self.reference.full_name}@{self.reference.ref}"

    def apply(self, new_sha: str, lines: List[str]) -> None:
        new_value = f"{self.reference.full_name}@{new_sha}"
        quote = self.quote
        rendered = f"{self.prefix}{quote}{new_value}{quote}{self.comment}{self.line_ending}"
        lines[self.line_index] = rendered
        self.value = new_value


class WorkflowFile:
    def __init__(self, path: Path, repo_slug: Optional[str]) -> None:
        self.path = path
        self.repo_slug = repo_slug.lower() if repo_slug else None
        self.lines = self._read_lines()
        self.usages: List[WorkflowUsage] = []
        self.skipped: List[Dict[str, str]] = []
        self._parse()

    def _read_lines(self) -> List[str]:
        with self.path.open("r", encoding="utf-8") as handle:
            return handle.read().splitlines(keepends=True)

    def _parse(self) -> None:
        for idx, line in enumerate(self.lines):
            usage = self._parse_line(idx, line)
            if usage is None:
                continue
            if isinstance(usage, dict):
                self.skipped.append(usage)
            else:
                self.usages.append(usage)

    def _parse_line(self, index: int, line: str) -> Optional[WorkflowUsage | Dict[str, str]]:
        body, line_ending = self._split_line(line)
        match = USES_REGEX.match(body)
        if not match:
            return None

        prefix = match.group("prefix")
        rest = match.group("rest")
        quote, value, comment = self._split_rest(rest)
        if value is None:
            return None
        if value.startswith("${{"):
            return None
        if value.startswith("./") or value.startswith("../"):
            return self._skip_record(value, "local-action")

        parsed = self._parse_action_reference(value)
        if not parsed:
            return None

        if self.repo_slug and parsed.full_name.lower().startswith(self.repo_slug):
            return self._skip_record(value, "current-repo")

        return WorkflowUsage(
            workflow_path=self.path,
            line_index=index,
            prefix=prefix,
            quote=quote,
            value=value,
            comment=comment,
            line_ending=line_ending,
            reference=parsed,
        )

    def _split_line(self, line: str) -> Tuple[str, str]:
        if line.endswith("\r\n"):
            return line[:-2], "\r\n"
        if line.endswith("\n"):
            return line[:-1], "\n"
        return line, ""

    def _split_rest(self, rest: str) -> Tuple[str, Optional[str], str]:
        rest = rest.rstrip()
        if not rest:
            return "", None, ""
        quote = ""
        comment = ""
        if rest[0] in ('"', "'"):
            quote = rest[0]
            end = 1
            while end < len(rest):
                if rest[end] == quote and rest[end - 1] != "\\":
                    break
                end += 1
            if end >= len(rest):
                value = rest[1:].strip()
                comment = ""
            else:
                value = rest[1:end].strip()
                comment = rest[end + 1 :]
        else:
            idx = None
            for pos, char in enumerate(rest):
                if char == "#" and (pos == 0 or rest[pos - 1].isspace()):
                    idx = pos
                    break
            if idx is not None:
                value = rest[:idx].strip()
                comment = rest[idx:]
            else:
                value = rest.strip()
                comment = ""
        if not value:
            return quote, None, comment
        if comment:
            comment = comment.rstrip()
            if comment and not comment.startswith("#") and not comment.startswith(" "):
                comment = " " + comment
        return quote, value, comment

    def _skip_record(self, value: str, reason: str) -> Dict[str, str]:
        return {
            "workflow": str(self.path),
            "uses": value,
            "reason": reason,
        }

    def _parse_action_reference(self, value: str) -> Optional[ActionReference]:
        match = ACTION_REGEX.match(value)
        if not match:
            return None
        return ActionReference(
            owner=match.group("owner"),
            repo=match.group("repo"),
            path=match.group("path") or "",
            ref=match.group("ref"),
        )

    def write(self) -> None:
        with self.path.open("w", encoding="utf-8") as handle:
            handle.writelines(self.lines)


class GitHubAPI:
    def __init__(self, token: Optional[str], timeout: float) -> None:
        self.token = token
        self.timeout = timeout

    def get_ref(self, owner: str, repo: str, namespace: str, ref: str) -> Dict[str, str]:
        encoded = quote(ref, safe="")
        path = f"/repos/{owner}/{repo}/git/ref/{namespace}/{encoded}"
        return self._request(path)

    def get_tag(self, owner: str, repo: str, sha: str) -> Dict[str, str]:
        path = f"/repos/{owner}/{repo}/git/tags/{sha}"
        return self._request(path)

    def get_commit(self, owner: str, repo: str, ref: str) -> Dict[str, str]:
        encoded = quote(ref, safe="")
        path = f"/repos/{owner}/{repo}/commits/{encoded}"
        return self._request(path)

    def _request(self, path: str) -> Dict[str, str]:
        url = f"https://api.github.com{path}"
        headers = {
            "Accept": "application/vnd.github+json",
            "User-Agent": "actions-lock-resolver",
        }
        if self.token:
            headers["Authorization"] = f"Bearer {self.token}"
        request = Request(url, headers=headers)
        try:
            with urlopen(request, timeout=self.timeout) as response:
                payload = response.read()
        except HTTPError as exc:
            if exc.code == 404:
                raise GitHubAPIError("Not found", transient=False) from exc
            raise GitHubAPIError(f"HTTP {exc.code}", transient=False) from exc
        except URLError as exc:  # pragma: no cover - network issues
            raise GitHubAPIError(str(exc), transient=True) from exc
        return json.loads(payload.decode("utf-8"))


class GitInterface:
    def __init__(self, *, cwd: Path) -> None:
        self.cwd = cwd

    def ls_remote(self, owner: str, repo: str, ref: str) -> str:
        url = f"https://github.com/{owner}/{repo}.git"
        proc = subprocess.run(
            ["git", "ls-remote", url, ref, f"{ref}^{{}}"],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            cwd=self.cwd,
        )
        if proc.returncode != 0:
            raise GitCLIError(proc.stderr.strip() or "git ls-remote failed", transient=True)

        commit_sha: Optional[str] = None
        tag_sha: Optional[str] = None
        for line in proc.stdout.splitlines():
            if not line:
                continue
            sha, name = line.split("\t", 1)
            if name.endswith("^{}"):
                commit_sha = sha
            else:
                tag_sha = sha
        if commit_sha:
            return commit_sha
        if tag_sha:
            return tag_sha
        raise GitCLIError("Reference not found via git ls-remote", transient=True)


class ActionsLockApply:
    def __init__(
        self,
        root: Path,
        *,
        github_api: GitHubAPI,
        git_interface: GitInterface,
        now_provider: Optional[Iterator[datetime]] = None,
    ) -> None:
        self.root = root
        self.github_api = github_api
        self.git_interface = git_interface
        self._now_provider = now_provider
        self.log_lines: List[str] = []
        self.skipped_entries: List[Dict[str, str]] = []
        self._cache: Dict[Tuple[str, str, str, str], Tuple[str, str]] = {}
        self.repo_slug = self._detect_repo_slug()

    def _now(self) -> datetime:
        if self._now_provider is not None:
            return next(self._now_provider)
        return utc_now()

    def _detect_repo_slug(self) -> Optional[str]:
        try:
            proc = subprocess.run(
                ["git", "config", "--get", "remote.origin.url"],
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                check=True,
                cwd=self.root,
            )
        except subprocess.CalledProcessError:
            return None
        url = proc.stdout.strip()
        if not url:
            return None
        if url.startswith("git@"):  # git@github.com:owner/repo.git
            _, path = url.split(":", 1)
        else:
            parsed = urlparse(url)
            path = parsed.path
        path = path.rstrip("/").removesuffix(".git")
        segments = [segment for segment in path.split("/") if segment]
        if len(segments) >= 2:
            return f"{segments[-2]}/{segments[-1]}"
        return None

    def collect_actions(self) -> Tuple[List[WorkflowUsage], Dict[Path, WorkflowFile]]:
        workflows: Dict[Path, WorkflowFile] = {}
        actions: List[WorkflowUsage] = []
        workflows_dir = self.root / WORKFLOWS_DIR
        if not workflows_dir.exists():
            return actions, workflows

        for path in sorted(workflows_dir.glob("*.yml")) + sorted(
            workflows_dir.glob("*.yaml")
        ):
            workflow = WorkflowFile(path, self.repo_slug)
            workflows[path] = workflow
            actions.extend(workflow.usages)
            self.skipped_entries.extend(
                {
                    "workflow": str(path.relative_to(self.root)),
                    "uses": entry["uses"],
                    "reason": entry["reason"],
                }
                for entry in workflow.skipped
            )
        return actions, workflows

    def resolve_usage(self, usage: WorkflowUsage) -> Tuple[str, str]:
        key = (
            usage.reference.owner,
            usage.reference.repo,
            usage.reference.path,
            usage.reference.ref,
        )
        if key in self._cache:
            return self._cache[key]

        ref = usage.reference.ref
        if is_sha(ref):
            result = (ref, "input")
        else:
            result = self._resolve_remote(usage.reference)
        if not is_sha(result[0]):
            raise ResolutionError(
                f"Resolved SHA for {usage.original_uses()} is invalid: {result[0]}"
            )
        self._cache[key] = result
        return result

    def _resolve_remote(self, reference: ActionReference) -> Tuple[str, str]:
        errors: List[str] = []
        try:
            sha = self._resolve_via_api(reference)
            return sha, "api"
        except GitHubAPIError as exc:
            errors.append(str(exc))
        try:
            sha = self.git_interface.ls_remote(
                reference.owner, reference.repo, reference.ref
            )
            return sha, "git"
        except GitCLIError as exc:
            errors.append(str(exc))
            raise ResolutionError(
                f"Unable to resolve {reference.full_name}@{reference.ref}: {'; '.join(errors)}",
                transient=True,
            ) from exc

    def _resolve_via_api(self, reference: ActionReference) -> str:
        for namespace in ("tags", "heads"):
            try:
                data = self.github_api.get_ref(
                    reference.owner, reference.repo, namespace, reference.ref
                )
            except GitHubAPIError as exc:
                if exc.transient:
                    raise
                continue
            obj = data.get("object", {})
            sha = obj.get("sha")
            obj_type = obj.get("type")
            if obj_type == "tag" and sha:
                return self._resolve_annotated_tag(reference, sha)
            if sha:
                return sha
        commit = self.github_api.get_commit(
            reference.owner, reference.repo, reference.ref
        )
        sha = commit.get("sha")
        if not sha:
            raise ResolutionError(
                f"Commit resolution failed for {reference.full_name}@{reference.ref}",
                transient=True,
            )
        return sha

    def _resolve_annotated_tag(self, reference: ActionReference, tag_sha: str) -> str:
        current = tag_sha
        for _ in range(5):
            tag = self.github_api.get_tag(reference.owner, reference.repo, current)
            obj = tag.get("object", {})
            sha = obj.get("sha")
            obj_type = obj.get("type")
            if obj_type == "commit" and sha:
                return sha
            if obj_type == "tag" and sha:
                current = sha
                continue
            if sha:
                return sha
        raise ResolutionError(
            f"Annotated tag resolution failed for {reference.full_name}@{reference.ref}",
            transient=True,
        )

    def apply(
        self,
        *,
        apply_changes: bool,
        commit_changes: bool,
        log_path: Path,
        report_path: Path,
    ) -> int:
        self.log_lines = []
        self.skipped_entries = []
        actions, workflows = self.collect_actions()
        stats = {"total": 0, "pinned": 0, "skipped_local": 0, "unchanged": 0}
        report = {
            "pinned": [],
            "unchanged": [],
            "skipped": [],
            "errors": [],
            "stats": stats,
        }

        for usage in actions:
            stats["total"] += 1
            try:
                sha, source = self.resolve_usage(usage)
            except ResolutionError as exc:
                self.log_lines.append(
                    f"{format_datetime(self._now())} [ERROR] {usage.original_uses()} :: {exc}"
                )
                report["errors"].append(
                    {
                        "workflow": str(usage.workflow_path.relative_to(self.root)),
                        "uses": usage.original_uses(),
                        "error": str(exc),
                    }
                )
                continue

            usage.resolved_sha = sha
            self.log_lines.append(
                f"{format_datetime(self._now())} [INFO] {usage.original_uses()} -> {sha} [{source}]"
            )

            cache_key = (
                usage.reference.owner,
                usage.reference.repo,
                usage.reference.path,
                usage.reference.ref,
            )
            if cache_key not in report.setdefault("_lock_entries", {}):
                report.setdefault("_lock_entries", {})[cache_key] = {
                    "uses": usage.reference.full_name,
                    "ref": usage.reference.ref,
                    "sha": sha,
                    "date": format_datetime(self._now()),
                    "author": LOCK_AUTHOR,
                    "rationale": LOCK_RATIONALE,
                }

            if usage.reference.ref == sha:
                stats["unchanged"] += 1
                report["unchanged"].append(
                    {
                        "workflow": str(usage.workflow_path.relative_to(self.root)),
                        "uses": usage.original_uses(),
                        "sha": sha,
                    }
                )
                continue

            stats["pinned"] += 1
            report["pinned"].append(
                {
                    "workflow": str(usage.workflow_path.relative_to(self.root)),
                    "uses": usage.original_uses(),
                    "sha": sha,
                }
            )
            if apply_changes:
                workflow = workflows[usage.workflow_path]
                usage.apply(sha, workflow.lines)

        report["skipped"].extend(self.skipped_entries)
        stats["skipped_local"] = len(self.skipped_entries)

        log_file = self.root / log_path
        report_file = self.root / report_path
        ensure_parent(log_file)
        ensure_parent(report_file)
        log_file.write_text("\n".join(self.log_lines), encoding="utf-8")
        lock_entries = report.pop("_lock_entries", {})
        report_copy = dict(report)
        report_file.write_text(json.dumps(report_copy, indent=2) + "\n", encoding="utf-8")

        if apply_changes:
            for workflow in workflows.values():
                workflow.write()

        self._write_lock(lock_entries)
        self._write_metadata(stats)

        if commit_changes:
            self._commit_changes(workflows.values(), report_copy)

        if apply_changes and report_copy["errors"]:
            return 2
        return 0

    def _write_lock(self, entries: Dict[Tuple[str, str, str, str], Dict[str, str]]) -> None:
        lock_path = self.root / LOCK_PATH
        ensure_parent(lock_path)
        sorted_entries = [
            entries[key]
            for key in sorted(
                entries,
                key=lambda item: f"{item[0]}/{item[1]}{item[2]}@{item[3]}",
            )
        ]
        lock_data = {
            "version": 1,
            "actions": sorted_entries,
            "metadata": {
                "sha": "",
                "date": format_datetime(self._now()),
                "author": METADATA_AUTHOR,
            },
        }
        placeholder_content = (json.dumps(lock_data, indent=2) + "\n").encode()
        metadata_sha = git_hash_object(placeholder_content, cwd=self.root)
        lock_data["metadata"]["sha"] = metadata_sha
        final_content = (json.dumps(lock_data, indent=2) + "\n").encode()
        lock_path.write_bytes(final_content)

    def _write_metadata(self, stats: Dict[str, int]) -> None:
        metadata_path = self.root / METADATA_PATH
        ensure_parent(metadata_path)
        payload = {
            "runner": {"python": "3.11", "platform": "${{ runner.os }}"},
            "stats": stats,
        }
        metadata_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    def _commit_changes(self, workflows: Iterable[WorkflowFile], report: Dict[str, Any]) -> None:
        self._ensure_clean_tree()
        paths = [
            LOCK_PATH,
            METADATA_PATH,
            OUT_DIR / "resolve.log",
            OUT_DIR / "report.json",
            *[wf.path.relative_to(self.root) for wf in workflows],
        ]
        subprocess.run(
            ["git", "add", *[str(path) for path in paths]],
            check=True,
            cwd=self.root,
        )
        pinned_lines = [f"- {item['uses']} -> {item['sha']}" for item in report["pinned"]]
        summary = [
            "Pin summary:",
            *pinned_lines,
            "",
            f"Total pinned: {report['stats']['pinned']}",
            f"Total unchanged: {report['stats']['unchanged']}",
        ]
        message = "chore(actions): pin GH Actions to immutable SHAs (S4 compliance)"
        subprocess.run(
            ["git", "commit", "-m", message, "-m", "\n".join(summary)],
            check=True,
            cwd=self.root,
        )

    def _ensure_clean_tree(self) -> None:
        proc = subprocess.run(
            ["git", "status", "--porcelain"],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            check=True,
            cwd=self.root,
        )
        if proc.stdout.strip():
            raise ActionsLockError("Working tree is dirty; aborting commit")


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--apply", action="store_true", help="Apply updates to workflows")
    parser.add_argument("--commit", action="store_true", help="Create a git commit")
    parser.add_argument(
        "--token-env",
        default="GITHUB_TOKEN",
        help="Environment variable to read GitHub token from (default: GITHUB_TOKEN)",
    )
    parser.add_argument(
        "--timeout",
        type=float,
        default=10.0,
        help="Timeout in seconds for GitHub API requests",
    )
    return parser


def run_cli(args: argparse.Namespace) -> int:
    if args.commit and not args.apply:
        raise ActionsLockError("--commit requires --apply")

    root = Path(__file__).resolve().parent.parent
    token = _select_token(args.token_env)
    github_api = GitHubAPI(token, timeout=args.timeout)
    git_interface = GitInterface(cwd=root)
    resolver = ActionsLockApply(root, github_api=github_api, git_interface=git_interface)
    if args.commit:
        resolver._ensure_clean_tree()

    return resolver.apply(
        apply_changes=args.apply,
        commit_changes=args.commit,
        log_path=OUT_DIR / "resolve.log",
        report_path=OUT_DIR / "report.json",
    )


def _select_token(preferred: Optional[str]) -> Optional[str]:
    candidates: List[str] = []
    if preferred:
        candidates.append(preferred)
    for fallback in ("GITHUB_TOKEN", "GH_TOKEN"):
        if fallback not in candidates:
            candidates.append(fallback)
    for name in candidates:
        value = os.environ.get(name)
        if value:
            return value
    return None


def main(argv: Optional[List[str]] = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    try:
        return run_cli(args)
    except ActionsLockError as exc:
        print(f"Error: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":  # pragma: no cover
    sys.exit(main())
