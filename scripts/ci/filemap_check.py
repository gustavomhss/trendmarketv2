from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, List

FILEMAP_SET = [
    ".github/workflows/s7-exec.yml",
    ".github/workflows/_s7-orr.yml",
    ".github/CODEOWNERS",
    ".github/dependabot.yml",
    "bin/preflight",
    "bin/setup_preflight_tools.sh",
    "data/raw",
    "data/log/log.jsonl",
    "docs/specs/s7/cap1_spec.md",
    "docs/specs/s7/cap2_gates.md",
    "docs/specs/s7/cap3_filemap.md",
    "schemas/v1/scorecard.schema.json",
    "schemas/v1/manifest.schema.json",
    "schemas/v1/t0_ruleset_sanity.schema.json",
    "schemas/v1/t1_yaml.schema.json",
    "schemas/v1/t2_security.schema.json",
    "schemas/v1/t3_pins.schema.json",
    "schemas/v1/t4_tests.schema.json",
    "schemas/v1/t5_props.schema.json",
    "schemas/v1/t6_determinism.schema.json",
    "schemas/v1/t7_append_only.schema.json",
    "scripts/ci/generate_actions_lock.py",
    "scripts/ci/validate_actions_lock.py",
    "scripts/ci/verify_action_commit_owners.py",
    "scripts/ci/ruleset_sanity.py",
    "scripts/crypto/sign_batch.py",
    "scripts/crypto/verify_batch.py",
    "scripts/det/check_determinism.py",
    "scripts/evidence/manifest.py",
    "scripts/evidence/pack.py",
    "scripts/evidence/verify_manifest.py",
    "scripts/merkle/merkle_build.py",
    "scripts/merkle/append_only_guard.py",
    "scripts/normalizer/normalize_batch.py",
    "scripts/scorecard/write.py",
    "tests/fixtures/crypto/test_ed25519_priv.pem",
    "tests/fixtures/crypto/test_ed25519_pub.pem",
    "tests/fixtures/data/dataset-a.json",
    "tests/fixtures/data/dataset-a.csv",
    "tests/fixtures/data/dataset-neg-domain-tag.json",
    "tests/fixtures/data/log-invalid-prev-root.jsonl",
    "tests/fixtures/expected/hashes_dataset_a.json",
    "tests/fixtures/expected/batch_sha256.txt",
    "tests/test_normalizer.py",
    "tests/test_merkle.py",
    "tests/test_signature.py",
    "tests/test_properties.py",
    ".editorconfig",
    ".gitleaks.toml",
    ".gitignore",
    ".yamllint.yml",
    "actions.lock",
    "CODEOWNERS",
    "LICENSE",
    "Makefile",
    "pyproject.toml",
    "README.md",
]


@dataclass
class Result:
    ok: bool
    missing: List[str]
    extra: List[str]

    def to_payload(self) -> dict:
        return {
            "ok": self.ok,
            "missing": self.missing,
            "extra": self.extra,
            "duration_ms": 0,
        }


def check_filemap(root: Path) -> Result:
    expected = {root / Path(item) for item in FILEMAP_SET}
    missing = sorted(str(path.relative_to(root)) for path in expected if not path.exists())
    ok = not missing
    return Result(ok=ok, missing=missing, extra=[])


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Validate Sprint 7 filemap")
    parser.add_argument("--root", default=".")
    parser.add_argument("--out", default="out/evidence/T1_yaml/filemap_check.json")
    return parser


def main(argv: Iterable[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(list(argv) if argv is not None else None)
    root = Path(args.root).resolve()
    result = check_filemap(root)
    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(result.to_payload(), separators=(",", ":")), encoding="utf-8")
    if not result.ok:
        print(json.dumps(result.to_payload(), separators=(",", ":")), file=sys.stderr)
        return 12
    return 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
