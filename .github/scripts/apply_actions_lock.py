#!/usr/bin/env python3
"""Apply pinned commits from actions.lock to workflow files."""

from __future__ import annotations

import argparse
import difflib
import re
import sys
from pathlib import Path
from typing import (
    Dict,
    Iterable,
    Iterator,
    List,
    Mapping,
    MutableMapping,
    Optional,
    Tuple,
)

try:
    import yaml  # type: ignore
except ModuleNotFoundError:  # pragma: no cover - fallback for environments sem PyYAML
    import sys
    from pathlib import Path

    sys.path.append(str(Path(__file__).resolve().parents[2]))
    import yaml_fallback as yaml  # type: ignore


USES_RE = re.compile(
    r"^(?P<prefix>\s*(?:-\s*)?uses:\s*)(?P<repo>[^@#\s][^@#\s]*/[^@#\s]+)@(?P<ref>[^\s#]+)(?P<space>\s*)(?P<comment>#.*)?$"
)
PIN_COMMENT_RE = re.compile(r"#\s*pinned\s*\(was\s+([^\)]+)\)", re.IGNORECASE)
HEX40_RE = re.compile(r"^[0-9a-f]{40}$")

LockEntry = Dict[str, str]


class LockError(RuntimeError):
    """Raised when the actions lock is malformed."""


def load_lock(lock_path: Path) -> Mapping[str, LockEntry]:
    if not lock_path.exists():
        raise LockError(f"actions.lock não encontrado: {lock_path}")
    try:
        payload = yaml.safe_load(lock_path.read_text(encoding="utf-8")) or {}
    except yaml.YAMLError as exc:  # pragma: no cover - yaml module detail
        raise LockError(f"YAML inválido em {lock_path}: {exc}") from exc

    actions = payload.get("actions")
    if not isinstance(actions, list):
        raise LockError("actions.lock inválido: campo actions ausente")

    mapping: Dict[str, LockEntry] = {}
    for item in actions:
        if not isinstance(item, MutableMapping):
            continue
        key = str(item.get("key") or "").strip()
        commit = str(item.get("commit") or "").strip().lower()
        if not key or not HEX40_RE.fullmatch(commit):
            continue
        mapping[key] = dict(item)
        repo, _, _ref = key.partition("@")
        mapping[f"{repo}@{commit}"] = dict(item)
        resolved = str(item.get("resolved") or "").strip()
        if resolved:
            mapping[f"{repo}@{resolved}"] = dict(item)
    return mapping


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


def _extract_original_ref(
    ref: str, comment: str | None, repo: str, lockmap: Mapping[str, LockEntry]
) -> str:
    if comment:
        comment_match = PIN_COMMENT_RE.search(comment)
        if comment_match:
            candidate = comment_match.group(1).strip()
            if candidate:
                return candidate
    # If commit pinned, prefer lock entry key to retrieve original ref
    entry = lockmap.get(f"{repo}@{ref}")
    if entry:
        key = str(entry.get("key") or "")
        if "@" in key:
            return key.split("@", 1)[1]
    return ref


def _choose_entry(
    repo: str, ref: str, lockmap: Mapping[str, LockEntry]
) -> Optional[LockEntry]:
    key = f"{repo}@{ref}"
    entry = lockmap.get(key)
    if entry:
        return entry
    if ref.count(".") >= 1:
        major = ref.split(".")[0]
        if major:
            entry = lockmap.get(f"{repo}@{major}")
            if entry:
                return entry
    return lockmap.get(f"{repo}@{ref.lower()}")


def pin_uses_line(
    line: str, lockmap: Mapping[str, LockEntry]
) -> Tuple[str, bool, Optional[str]]:
    stripped = line.rstrip("\r\n")
    match = USES_RE.match(stripped)
    if not match:
        return line, False, None
    repo = match.group("repo")
    if repo.startswith("./") or repo.startswith(".\\"):
        return line, False, None
    ref = match.group("ref")
    comment = match.group("comment")
    original_ref = _extract_original_ref(ref, comment, repo, lockmap)
    entry = _choose_entry(repo, original_ref, lockmap)
    if entry is None:
        entry = _choose_entry(repo, ref, lockmap)
    if entry is None:
        return line, False, f"entrada não encontrada no lock para {repo}@{original_ref}"
    commit = str(entry.get("commit") or "").lower()
    if not HEX40_RE.fullmatch(commit):
        return line, False, f"commit inválido para {repo}@{original_ref}"
    comment_ref = entry.get("key", f"{repo}@{original_ref}").split("@", 1)[1]
    if ref.lower() == commit and comment:
        desired_comment = f"# pinned (was {comment_ref})"
        if comment.strip().lower() == desired_comment.lower():
            return line, False, None
    prefix = match.group("prefix")
    space = match.group("space") or "  "
    if space.strip():
        space = "  "
    new_line = f"{prefix}{repo}@{commit}{space}# pinned (was {comment_ref})"
    newline = line[len(stripped) :]
    return new_line + newline, True, None


def process_file(
    path: Path, lockmap: Mapping[str, LockEntry]
) -> Tuple[bool, List[str], List[str]]:
    try:
        original_text = path.read_text(encoding="utf-8")
    except OSError as exc:
        return False, [], [f"falha ao ler {path}: {exc}"]
    lines = original_text.splitlines(keepends=True)
    changed = False
    warnings: List[str] = []
    new_lines: List[str] = []
    for line in lines:
        new_line, line_changed, warning = pin_uses_line(line, lockmap)
        if warning:
            warnings.append(f"{path}: {warning}")
        if line_changed:
            changed = True
        new_lines.append(new_line)
    if not changed:
        return False, warnings, []
    new_text = "".join(new_lines)
    try:
        path.write_text(new_text, encoding="utf-8")
    except OSError as exc:
        raise LockError(f"falha ao escrever {path}: {exc}") from exc
    diff = list(
        difflib.unified_diff(
            original_text.splitlines(),
            new_text.splitlines(),
            fromfile=str(path),
            tofile=str(path),
            lineterm="",
        )
    )
    return True, warnings, diff


def main(argv: Optional[Iterable[str]] = None) -> int:
    parser = argparse.ArgumentParser(description="Apply pinned SHAs from actions.lock")
    parser.add_argument(
        "--lock", default=".github/actions.lock", help="path to actions.lock"
    )
    parser.add_argument(
        "--root", default=".", help="repository root to scan for workflow files"
    )
    args = parser.parse_args(list(argv) if argv is not None else None)

    root = Path(args.root).resolve()
    lock_path = (root / args.lock).resolve()
    try:
        lockmap = load_lock(lock_path)
    except LockError as exc:
        print(f"[apply] erro: {exc}")
        return 2

    changed_files: List[Path] = []
    warnings: List[str] = []
    diffs: List[str] = []

    for path in iter_yaml_files(root):
        changed, file_warnings, diff_lines = process_file(path, lockmap)
        warnings.extend(file_warnings)
        if changed:
            changed_files.append(path)
            diffs.extend(diff_lines)

    for warning in warnings:
        print(f"[warn] {warning}")

    if not changed_files:
        print("[apply] Nenhuma alteração necessária")
        return 0

    print("[apply] Arquivos atualizados:")
    for path in changed_files:
        print(f"  - {path.relative_to(root)}")
    if diffs:
        print("[apply] Diff resumido:")
        for line in diffs:
            print(line)
    return 10


if __name__ == "__main__":
    sys.exit(main())
