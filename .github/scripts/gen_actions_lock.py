#!/usr/bin/env python3
"""Generate a deterministic YAML lockfile for GitHub Actions usages."""

from __future__ import annotations

import argparse
import dataclasses
import os
import re
import subprocess
import sys
from collections import defaultdict
from datetime import datetime, timezone
from pathlib import Path
from typing import (
    Dict,
    Iterator,
    List,
    Mapping,
    MutableMapping,
    Optional,
    Sequence,
    Tuple,
)

try:
    import yaml  # type: ignore
except ModuleNotFoundError:  # pragma: no cover
    import sys

    sys.path.append(str(Path(__file__).resolve().parents[2]))
    import yaml_fallback as yaml  # type: ignore

USES_RE = re.compile(
    r"^(?P<prefix>\s*(?:-\s*)?uses:\s*)(?P<repo>[^@#\s][^@#\s]*/[^@#\s]+)@(?P<ref>[^\s#]+)(?P<space>\s*)(?P<comment>#.*)?$"
)
LOCAL_PREFIXES = ("./", ".\\", "docker://")
HEX40_RE = re.compile(r"^[0-9a-f]{40}$", re.IGNORECASE)
SEMVER_MAJOR_RE = re.compile(r"^v?(\d+)$")


@dataclasses.dataclass(frozen=True)
class LockEntry:
    key: str
    commit: str
    source: str
    resolved: Optional[str]
    checked_at: str


class LockGenerationError(RuntimeError):
    """Raised when lock generation fails."""


def isoformat_now() -> str:
    return (
        datetime.now(timezone.utc)
        .replace(microsecond=0)
        .isoformat()
        .replace("+00:00", "Z")
    )


def git_head_sha() -> str:
    try:
        return (
            subprocess.check_output(["git", "rev-parse", "HEAD"], text=True)
            .strip()
            .lower()
        )
    except subprocess.CalledProcessError:
        return "0" * 40


def iter_yaml_files(root: Path) -> Iterator[Path]:
    workflows = root / ".github" / "workflows"
    if workflows.exists():
        for path in sorted(workflows.rglob("*.yml")):
            yield path
        for path in sorted(workflows.rglob("*.yaml")):
            if path.suffix != ".yml":
                yield path
    actions_dir = root / ".github" / "actions"
    if actions_dir.exists():
        for pattern in ("action.yml", "action.yaml"):
            for path in sorted(actions_dir.rglob(pattern)):
                yield path


def extract_uses(path: Path) -> Iterator[Tuple[str, str]]:
    try:
        text = path.read_text(encoding="utf-8")
    except OSError as exc:
        raise LockGenerationError(f"falha ao ler {path}: {exc}") from exc
    for raw_line in text.splitlines():
        match = USES_RE.match(raw_line.strip())
        if not match:
            continue
        repo = match.group("repo")
        if repo.startswith(LOCAL_PREFIXES):
            continue
        ref = match.group("ref")
        yield repo, ref


def collect_uses(root: Path) -> List[Tuple[str, str]]:
    seen: Dict[str, set[str]] = defaultdict(set)
    results: List[Tuple[str, str]] = []
    for file_path in iter_yaml_files(root):
        for repo, ref in extract_uses(file_path):
            if ref not in seen[repo]:
                seen[repo].add(ref)
                results.append((repo, ref))
    return sorted(results, key=lambda item: (item[0].lower(), item[1].lower()))


def ls_remote(owner: str, repo: str) -> Mapping[str, str]:
    url = f"https://github.com/{owner}/{repo}.git"
    try:
        output = subprocess.check_output(
            ["git", "ls-remote", "--tags", "--heads", url],
            text=True,
        )
    except subprocess.CalledProcessError as exc:
        raise LockGenerationError(
            f"git ls-remote falhou para {owner}/{repo}: {exc}"
        ) from exc
    mapping: Dict[str, str] = {}
    for line in output.splitlines():
        if not line.strip():
            continue
        sha, ref = line.split("\t", 1)
        mapping[ref.strip()] = sha.strip().lower()
    return mapping


def parse_semver(tag: str) -> Tuple[Tuple[int, ...], int, str]:
    clean = tag.lstrip("v")
    main, sep, suffix = clean.partition("-")
    parts: List[int] = []
    for piece in main.split("."):
        if piece.isdigit():
            parts.append(int(piece))
        else:
            digits = "".join(ch for ch in piece if ch.isdigit())
            parts.append(int(digits) if digits else 0)
    return tuple(parts), 1 if not suffix else 0, suffix


def choose_major_tag(tags: Mapping[str, str], ref: str) -> Optional[Tuple[str, str]]:
    prefix = ref.rstrip(".") + "."
    candidates = [name for name in tags if name == ref or name.startswith(prefix)]
    if not candidates:
        return None
    best = max(candidates, key=lambda name: parse_semver(name))
    return best, tags[best]


def resolve_ref(
    repo: str, ref: str, cache: Dict[str, Mapping[str, str]]
) -> Tuple[str, str, Optional[str]]:
    parts = repo.split("/")
    if len(parts) < 2:
        raise LockGenerationError(f"referência uses inválida: {repo}")
    owner, project = parts[0], parts[1]
    cache_key = f"{owner}/{project}"
    if cache_key not in cache:
        cache[cache_key] = ls_remote(owner, project)
    mapping = cache[cache_key]

    if HEX40_RE.fullmatch(ref):
        return ref.lower(), "sha", None

    tag_ref = f"refs/tags/{ref}"
    if tag_ref in mapping:
        return mapping[tag_ref], "tag", None

    annotated_ref = f"refs/tags/{ref}^{{}}"
    if annotated_ref in mapping:
        return mapping[annotated_ref], "tag", None

    major_match = SEMVER_MAJOR_RE.fullmatch(ref)
    if major_match:
        tags: Dict[str, str] = {}
        for name, sha in mapping.items():
            if not name.startswith("refs/tags/"):
                continue
            base = name[len("refs/tags/") :]
            if base.endswith("^{}"):
                base = base[:-3]
                tags[base] = sha
            else:
                tags.setdefault(base, sha)
        result = choose_major_tag(tags, f"v{major_match.group(1)}")
        if result:
            resolved_tag, sha = result
            return sha, "tag", resolved_tag

    head_ref = f"refs/heads/{ref}"
    if head_ref in mapping:
        return mapping[head_ref], "branch", None

    direct = mapping.get(ref)
    if direct:
        return direct, "ref", None

    raise LockGenerationError(f"não foi possível resolver {repo}@{ref}")


def build_entries(
    root: Path,
    refs: List[Tuple[str, str]],
    existing: Mapping[str, MutableMapping[str, object]],
) -> List[LockEntry]:
    cache: Dict[str, Mapping[str, str]] = {}
    entries: List[LockEntry] = []
    checked_at = isoformat_now()
    for repo, ref in refs:
        key = f"{repo}@{ref}"
        try:
            sha, source, resolved = resolve_ref(repo, ref, cache)
        except LockGenerationError as exc:
            cached = existing.get(key)
            if not cached:
                raise
            sha = str(cached.get("commit") or "").lower()
            if not HEX40_RE.fullmatch(sha):
                raise
            source = str(cached.get("source") or "cached")
            resolved = str(cached.get("resolved") or "").strip() or None
            print(f"[gen] usando cache para {key}: {sha} ({exc})")
        entries.append(
            LockEntry(
                key=key,
                commit=sha,
                source=source,
                resolved=resolved,
                checked_at=checked_at,
            )
        )
    entries.sort(key=lambda item: item.key.lower())
    return entries


def load_existing_lock(path: Path) -> Dict[str, MutableMapping[str, object]]:
    if not path.exists():
        return {}
    try:
        data = yaml.safe_load(path.read_text(encoding="utf-8")) or {}
    except yaml.YAMLError:
        return {}
    actions = data.get("actions")
    if not isinstance(actions, list):
        return {}
    cache: Dict[str, MutableMapping[str, object]] = {}
    for item in actions:
        if not isinstance(item, MutableMapping):
            continue
        key = str(item.get("key") or "").strip()
        commit = str(item.get("commit") or "").strip().lower()
        if key and commit:
            cache[key] = dict(item)
    return cache


def merge_with_existing(
    new_entries: List[LockEntry], existing: Mapping[str, MutableMapping[str, object]]
) -> List[Dict[str, object]]:
    merged: List[Dict[str, object]] = []
    for entry in new_entries:
        payload = {
            "key": entry.key,
            "commit": entry.commit,
            "source": entry.source,
            "checked_at": entry.checked_at,
        }
        if entry.resolved and entry.resolved != entry.key.split("@", 1)[1]:
            payload["resolved"] = entry.resolved
        old = existing.get(entry.key)
        if old and old.get("commit") == entry.commit:
            for key in ("resolved", "note"):
                if key in old and key not in payload:
                    payload[key] = old[key]
            if "checked_at" in old:
                payload["checked_at"] = old["checked_at"]
        merged.append(payload)
    return merged


def dump_lock(
    path: Path, entries: List[Dict[str, object]], author: str, rationale: str
) -> None:
    payload = {
        "version": 2,
        "generated": {
            "author": author,
            "reason": rationale,
            "sha": git_head_sha(),
            "date": isoformat_now(),
        },
        "actions": entries,
    }
    text = yaml.safe_dump(payload, sort_keys=False)
    if not text.endswith("\n"):
        text += "\n"
    path.write_text(text, encoding="utf-8")


def parse_args(argv: Optional[Sequence[str]]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate actions.lock from workflow usages"
    )
    parser.add_argument("--root", default=".")
    parser.add_argument("--lock", default=".github/actions.lock")
    parser.add_argument(
        "--rationale",
        default="Pin de Actions para reprodutibilidade",
    )
    parser.add_argument(
        "--author",
        default=os.environ.get("GITHUB_ACTOR", "CI"),
    )
    return parser.parse_args(list(argv) if argv is not None else None)


def main(argv: Optional[Sequence[str]] = None) -> int:
    args = parse_args(argv)
    root = Path(args.root).resolve()
    lock_path = (root / args.lock).resolve()

    refs = collect_uses(root)
    if not refs:
        print("[gen] Nenhuma referência externa encontrada")
        dump_lock(lock_path, [], args.author, args.rationale)
        return 0

    existing = load_existing_lock(lock_path)
    try:
        entries = build_entries(root, refs, existing)
    except LockGenerationError as exc:
        print(f"[gen] erro: {exc}")
        if existing:
            print("[gen] mantendo lock existente")
            return 1
        raise

    merged = merge_with_existing(entries, existing)
    dump_lock(lock_path, merged, args.author, args.rationale)
    print(f"[gen] lock gerado com {len(merged)} entradas em {lock_path}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
