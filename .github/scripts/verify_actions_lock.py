#!/usr/bin/env python3
"""Validate actions.lock and ensure workflows stay pinned to recorded SHAs."""

from __future__ import annotations

import argparse
import re
import sys
from dataclasses import dataclass
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
PIN_COMMENT_RE = re.compile(r"#\s*pinned\s*\(was\s+([^\)]+)\)", re.IGNORECASE)
HEX40_RE = re.compile(r"^[0-9a-f]{40}$")
ISO_ZULU_RE = re.compile(r"^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z$")
LOCAL_PREFIXES = ("./", ".\\", "docker://")


@dataclass(frozen=True)
class LockRecord:
    repo: str
    commit: str
    preferred_ref: str
    resolved: Optional[str]


class ValidationError(RuntimeError):
    """Raised when validation fails."""


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


def load_lock(lock_path: Path) -> Tuple[Mapping[str, LockRecord], Dict[str, object]]:
    if not lock_path.exists():
        raise ValidationError(f"actions.lock não encontrado: {lock_path}")
    try:
        payload = yaml.safe_load(lock_path.read_text(encoding="utf-8")) or {}
    except yaml.YAMLError as exc:
        raise ValidationError(f"YAML inválido: {exc}") from exc

    if not isinstance(payload, MutableMapping):
        raise ValidationError("Formato inválido: raiz precisa ser objeto")

    version = payload.get("version")
    if version not in (1, 2):
        raise ValidationError("actions.lock: campo version inválido")

    generated = payload.get("generated") or payload.get("metadata")
    if not isinstance(generated, MutableMapping):
        raise ValidationError("actions.lock: metadata/generated ausente")

    for key in ("sha", "date"):
        if key not in generated:
            raise ValidationError(f"actions.lock: campo generated.{key} ausente")
    sha_value = str(generated.get("sha") or "").strip().lower()
    if not HEX40_RE.fullmatch(sha_value):
        raise ValidationError("actions.lock: sha inválido")
    date_value = str(generated.get("date") or "").strip()
    if not ISO_ZULU_RE.fullmatch(date_value):
        raise ValidationError("actions.lock: date inválido")

    actions = payload.get("actions")
    if not isinstance(actions, list) or not actions:
        raise ValidationError("actions.lock: campo actions ausente ou vazio")

    mapping: Dict[str, LockRecord] = {}
    for item in actions:
        if not isinstance(item, MutableMapping):
            raise ValidationError("actions[*]: objeto inválido")
        key = str(item.get("key") or "").strip()
        commit = str(item.get("commit") or "").strip().lower()
        source = str(item.get("source") or "").strip()
        checked_at = str(item.get("checked_at") or "").strip()
        if not key or "@" not in key:
            raise ValidationError("actions[*]: key inválida")
        if not HEX40_RE.fullmatch(commit):
            raise ValidationError(f"actions[{key}]: commit inválido")
        if not source:
            raise ValidationError(f"actions[{key}]: source ausente")
        if checked_at and not ISO_ZULU_RE.fullmatch(checked_at):
            raise ValidationError(f"actions[{key}]: checked_at inválido")
        repo, _, ref = key.partition("@")
        record = LockRecord(
            repo=repo,
            commit=commit,
            preferred_ref=ref,
            resolved=str(item.get("resolved") or "").strip() or None,
        )
        mapping[key] = record
        mapping[f"{repo}@{commit}"] = record
        if record.resolved:
            mapping[f"{repo}@{record.resolved}"] = record
    return mapping, dict(payload)


def parse_uses_line(line: str) -> Optional[Tuple[str, str, str, Optional[str]]]:
    stripped = line.rstrip("\r\n")
    match = USES_RE.match(stripped)
    if not match:
        return None
    repo = match.group("repo")
    if repo.startswith(LOCAL_PREFIXES):
        return None
    ref = match.group("ref").strip()
    comment = match.group("comment")
    return repo, ref, stripped, comment


def expected_ref(repo: str, comment: Optional[str], lock_entry: LockRecord) -> str:
    if comment:
        match = PIN_COMMENT_RE.search(comment)
        if match:
            candidate = match.group(1).strip()
            if candidate:
                return candidate
    if lock_entry.resolved:
        return lock_entry.resolved
    return lock_entry.preferred_ref


def validate_workflows(root: Path, lockmap: Mapping[str, LockRecord]) -> List[str]:
    errors: List[str] = []
    for path in iter_yaml_files(root):
        try:
            lines = path.read_text(encoding="utf-8").splitlines()
        except OSError as exc:
            errors.append(f"falha ao ler {path}: {exc}")
            continue
        for line in lines:
            parsed = parse_uses_line(line)
            if not parsed:
                continue
            repo, ref, _, comment = parsed
            if not HEX40_RE.fullmatch(ref.lower()):
                errors.append(
                    f"{path}: referência não pinada para {repo}@{ref}. Rode apply_actions_lock.py"
                )
                continue
            entry = lockmap.get(f"{repo}@{ref.lower()}")
            if entry is None and comment:
                match = PIN_COMMENT_RE.search(comment)
                if match:
                    original = match.group(1).strip()
                    entry = lockmap.get(f"{repo}@{original}")
            if entry is None:
                errors.append(
                    f"{path}: SHA {ref} não encontrado no actions.lock para {repo}"
                )
                continue
            if entry.commit != ref.lower():
                errors.append(
                    f"{path}: SHA {ref} diverge do lock ({entry.commit}) para {repo}"
                )
                continue
            if not comment:
                errors.append(
                    f"{path}: comentário '# pinned (was ...)' ausente para {repo}@{ref}"
                )
                continue
            if "pinned" not in comment.lower():
                errors.append(
                    f"{path}: comentário inválido para {repo}@{ref}; esperado '# pinned (was ...)'."
                )
                continue
            expected = expected_ref(repo, comment, entry)
            if expected not in comment:
                errors.append(
                    f"{path}: comentário pin inconsistente para {repo}@{ref}."
                )
    return errors


def parse_args(argv: Optional[Sequence[str]]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Verify actions.lock consistency")
    parser.add_argument("--lock", default=".github/actions.lock")
    parser.add_argument("--root", default=".")
    parser.add_argument(
        "--report",
        default="out/guard/s4/actions_lock_report.yml",
        help="arquivo de relatório opcional",
    )
    return parser.parse_args(list(argv) if argv is not None else None)


def write_report(report_path: Path, status: str, details: Mapping[str, object]) -> None:
    report_path.parent.mkdir(parents=True, exist_ok=True)
    payload = {"status": status, **details}
    report_path.write_text(yaml.safe_dump(payload, sort_keys=False), encoding="utf-8")


def main(argv: Optional[Sequence[str]] = None) -> int:
    args = parse_args(argv)
    root = Path(args.root).resolve()
    lock_path = (root / args.lock).resolve()
    report_path = (root / args.report).resolve()

    try:
        lockmap, raw_lock = load_lock(lock_path)
    except ValidationError as exc:
        write_report(report_path, "fail", {"error": str(exc)})
        print(f"[verify] erro: {exc}")
        return 3

    errors = validate_workflows(root, lockmap)
    if errors:
        write_report(report_path, "fail", {"errors": errors})
        for error in errors:
            print(f"[verify] {error}")
        return 4

    write_report(report_path, "pass", {"actions": list(raw_lock.get("actions", []))})
    print("[verify] actions.lock consistente com workflows")
    return 0


if __name__ == "__main__":
    sys.exit(main())
