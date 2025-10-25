#!/usr/bin/env python3
"""Create the s5 status bundle with offline dbt artefacts."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import zipfile

REPO_ROOT = Path(__file__).resolve().parents[1]
OUT_DIR = REPO_ROOT / "out"
TARGET_DIR = REPO_ROOT / "target"
BUNDLE_PATH = OUT_DIR / "s5-status-bundle.zip"
CHECKSUM_PATH = OUT_DIR / "s5-status-bundle.sha256.txt"

INCLUDE_PATHS = [
    TARGET_DIR / "manifest.json",
    TARGET_DIR / "run_results.json",
    TARGET_DIR / "invocation_id.txt",
    OUT_DIR / "dbt" / "ce.duckdb",
    OUT_DIR / "logs" / "dbt_offline_runner.log",
]


def ensure_artifact_exists(path: Path) -> None:
    if not path.exists():
        raise FileNotFoundError(f"required artefact missing: {path}")


def build_bundle() -> None:
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    with zipfile.ZipFile(BUNDLE_PATH, "w", compression=zipfile.ZIP_DEFLATED) as zf:
        for artifact in INCLUDE_PATHS:
            ensure_artifact_exists(artifact)
            zf.write(artifact, artifact.relative_to(REPO_ROOT).as_posix())


def compute_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def write_checksum(hash_value: str) -> None:
    payload = json.dumps(
        {"file": BUNDLE_PATH.relative_to(REPO_ROOT).as_posix(), "sha256": hash_value},
        indent=2,
    ) + "\n"
    CHECKSUM_PATH.write_text(payload, encoding="utf-8")


def main() -> int:
    build_bundle()
    hash_value = compute_sha256(BUNDLE_PATH)
    write_checksum(hash_value)
    print(f"Created bundle {BUNDLE_PATH} with sha256 {hash_value}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
