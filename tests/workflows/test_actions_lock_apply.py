"""Regression tests ensuring actions.lock pins are enforced in workflows."""

from __future__ import annotations

import importlib.util
import re
import sys
from pathlib import Path
from typing import Dict, Iterator

import pytest

try:
    import yaml  # type: ignore
except ModuleNotFoundError:  # pragma: no cover
    ROOT_FALLBACK = Path(__file__).resolve().parents[2]
    sys.path.append(str(ROOT_FALLBACK))
    import yaml_fallback as yaml  # type: ignore

ROOT = Path(__file__).resolve().parents[2]
APPLY_PATH = ROOT / ".github" / "scripts" / "apply_actions_lock.py"
LOCK_PATH = ROOT / ".github" / "actions.lock"
USES_RE = re.compile(
    r"^(?P<prefix>\s*(?:-\s*)?uses:\s*)(?P<repo>[^@#\s][^@#\s]*/[^@#\s]+)@(?P<ref>[^\s#]+)(?P<space>\s*)(?P<comment>#.*)?$"
)
PIN_COMMENT_RE = re.compile(r"#\s*pinned\s*\(was\s+([^\)]+)\)", re.IGNORECASE)
HEX40_RE = re.compile(r"^[0-9a-f]{40}$")
LOCAL_PREFIXES = ("./", ".\\", "docker://")


@pytest.fixture(scope="module")
def apply_module():
    spec = importlib.util.spec_from_file_location("apply_actions_lock", APPLY_PATH)
    assert spec and spec.loader
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


@pytest.fixture(scope="module")
def lock_map() -> Dict[str, dict]:
    data = yaml.safe_load(LOCK_PATH.read_text(encoding="utf-8"))
    mapping: Dict[str, dict] = {}
    for item in data.get("actions", []):
        key = item["key"]
        commit = item["commit"].lower()
        repo = key.split("@", 1)[0]
        mapping[key] = item
        mapping[f"{repo}@{commit}"] = item
        resolved = item.get("resolved")
        if resolved:
            mapping[f"{repo}@{resolved}"] = item
    return mapping


def iter_yaml_files() -> Iterator[Path]:
    workflows = ROOT / ".github" / "workflows"
    if workflows.exists():
        yield from sorted(workflows.rglob("*.yml"))
        for path in sorted(workflows.rglob("*.yaml")):
            if path.suffix != ".yml":
                yield path
    actions_dir = ROOT / ".github" / "actions"
    if actions_dir.exists():
        for pattern in ("action.yml", "action.yaml"):
            yield from sorted(actions_dir.rglob(pattern))


def extract_uses(path: Path) -> Iterator[tuple[str, str, str]]:
    for raw_line in path.read_text(encoding="utf-8").splitlines():
        match = USES_RE.match(raw_line)
        if not match:
            continue
        repo = match.group("repo")
        if repo.startswith(LOCAL_PREFIXES):
            continue
        ref = match.group("ref")
        comment = match.group("comment") or ""
        yield repo, ref, comment


def test_every_use_is_pinned(lock_map: Dict[str, dict]) -> None:
    missing: list[str] = []
    for file_path in iter_yaml_files():
        for repo, ref, comment in extract_uses(file_path):
            if not HEX40_RE.fullmatch(ref.lower()):
                missing.append(f"{file_path}: {repo}@{ref} não está pinado")
                continue
            if "pinned" not in comment.lower():
                missing.append(f"{file_path}: comentário pin ausente para {repo}@{ref}")
                continue
            match = PIN_COMMENT_RE.search(comment)
            if not match:
                missing.append(
                    f"{file_path}: comentário inválido '# pinned (was ...)' para {repo}@{ref}"
                )
                continue
            original = match.group(1).strip()
            entry = lock_map.get(f"{repo}@{ref.lower()}") or lock_map.get(
                f"{repo}@{original}"
            )
            if not entry:
                missing.append(f"{file_path}: lock ausente para {repo}@{ref}")
                continue
            if entry["commit"].lower() != ref.lower():
                missing.append(
                    f"{file_path}: SHA {ref} diverge do lock ({entry['commit']}) para {repo}"
                )
    assert not missing, "\n".join(missing)


def test_apply_line_is_idempotent(apply_module, lock_map: Dict[str, dict]) -> None:
    checkout_entry = lock_map.get("actions/checkout@v4")
    if checkout_entry is None:
        pytest.skip("Entrada de checkout@v4 não encontrada no lock")
    commit = checkout_entry["commit"].lower()
    line = f"      - uses: actions/checkout@{commit}  # pinned (was v4)\n"
    new_line, changed, warning = apply_module.pin_uses_line(line, lock_map)
    assert new_line == line
    assert not changed
    assert warning is None


def test_apply_line_from_major_tag(apply_module, lock_map: Dict[str, dict]) -> None:
    target = None
    for entry in lock_map.values():
        if "@v" in entry["key"]:
            target = entry
            break
    if target is None:
        pytest.skip("Nenhuma ref major encontrada no lock")
    repo = target["key"].split("@", 1)[0]
    major = target["key"].split("@", 1)[1]
    line = f"  uses: {repo}@{major}\n"
    new_line, changed, warning = apply_module.pin_uses_line(line, lock_map)
    assert changed
    assert warning is None
    assert "# pinned (was" in new_line
    match = USES_RE.match(new_line.strip())
    assert match is not None
    assert HEX40_RE.fullmatch(match.group("ref"))
