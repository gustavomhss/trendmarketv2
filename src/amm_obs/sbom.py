"""Deterministic CycloneDX SBOM generation for TrendMarket observability."""
from __future__ import annotations

import hashlib
import json
import subprocess
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, List, Optional


class SBOMGenerationError(RuntimeError):
    """Raised when the repository context cannot be determined."""


@dataclass(frozen=True)
class _GitInfo:
    repo_name: str
    commit: str
    branch: str
    commit_time: str
    remote_url: Optional[str]


def _run_git(args: List[str], *, repo_root: Path) -> str:
    result = subprocess.run(
        ["git", *args],
        cwd=str(repo_root),
        check=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    return result.stdout.strip()


def _safe_run_git(args: List[str], *, repo_root: Path) -> Optional[str]:
    try:
        value = _run_git(args, repo_root=repo_root)
    except subprocess.CalledProcessError:
        return None
    return value or None


def _git_info(repo_root: Path) -> _GitInfo:
    try:
        commit = _run_git(["rev-parse", "HEAD"], repo_root=repo_root)
    except subprocess.CalledProcessError as exc:  # pragma: no cover - fatal error
        raise SBOMGenerationError("git commit hash not available") from exc

    branch = _safe_run_git(["rev-parse", "--abbrev-ref", "HEAD"], repo_root=repo_root) or "HEAD"
    commit_time = (
        _safe_run_git(["show", "-s", "--format=%cI", "HEAD"], repo_root=repo_root)
        or "1970-01-01T00:00:00Z"
    )
    remote_url = _safe_run_git(["config", "--get", "remote.origin.url"], repo_root=repo_root)
    repo_name = repo_root.name
    return _GitInfo(
        repo_name=repo_name,
        commit=commit,
        branch=branch,
        commit_time=commit_time,
        remote_url=remote_url,
    )


def _serial_number(seed: str) -> str:
    digest = hashlib.sha256(seed.encode("utf-8")).hexdigest()
    uuid = f"{digest[:8]}-{digest[8:12]}-{digest[12:16]}-{digest[16:20]}-{digest[20:32]}"
    return f"urn:uuid:{uuid}"


def _component(info: _GitInfo) -> Dict[str, Any]:
    bom_ref = f"pkg:git/{info.repo_name}@{info.commit}"
    properties = [
        {"name": "git.branch", "value": info.branch},
        {"name": "git.commit", "value": info.commit},
        {"name": "git.commit_time", "value": info.commit_time},
    ]
    if info.remote_url:
        properties.append({"name": "git.remote", "value": info.remote_url})

    component: Dict[str, Any] = {
        "type": "application",
        "bom-ref": bom_ref,
        "name": info.repo_name,
        "version": info.commit,
        "purl": bom_ref,
        "properties": properties,
    }
    return component


def generate_sbom(output_path: Path, *, repo_root: Optional[Path] = None) -> Dict[str, Any]:
    """Generate a deterministic CycloneDX SBOM and persist it to ``output_path``."""

    root = repo_root.resolve() if repo_root is not None else Path(__file__).resolve().parents[2]
    info = _git_info(root)
    component = _component(info)

    bom: Dict[str, Any] = {
        "bomFormat": "CycloneDX",
        "specVersion": "1.4",
        "serialNumber": _serial_number(info.commit),
        "version": 1,
        "metadata": {
            "timestamp": info.commit_time,
            "component": component,
            "tools": [
                {
                    "vendor": "trendmarketv2",
                    "name": "obs_sbom",
                    "version": "1.0.0",
                }
            ],
        },
        "components": [component],
        "dependencies": [
            {
                "ref": component["bom-ref"],
                "dependsOn": [],
            }
        ],
    }

    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(json.dumps(bom, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return bom


__all__ = ["generate_sbom", "SBOMGenerationError"]
