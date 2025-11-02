from __future__ import annotations

import argparse
import hashlib
import json
import tempfile
from pathlib import Path
from typing import Iterable, Tuple

from scripts.evidence.pack import write_zip
from scripts.normalizer.normalize_batch import canonical_json

EXPECTED_HASHES = Path("tests/fixtures/expected/hashes_dataset_a.json")
EXPECTED_BATCH_SHA = Path("tests/fixtures/expected/batch_sha256.txt")
DEFAULT_BATCH = Path("out/normalized/batch.json")
DEFAULT_OUT = Path("out/evidence/T6_determinism/compare.json")
DEFAULT_DIR = Path("out/evidence/T6_determinism")


def load_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def load_expected() -> Tuple[dict, str]:
    hashes = load_json(EXPECTED_HASHES)
    batch_sha = EXPECTED_BATCH_SHA.read_text(encoding="utf-8").strip()
    return hashes, batch_sha


def compute_actual(batch_path: Path) -> Tuple[dict, str]:
    batch = load_json(batch_path)
    records = batch.get("records", [])
    leaves = [hashlib.sha256(canonical_json(record)).hexdigest() for record in records]
    root = batch.get("root")
    entries_hash = batch.get("entries_hash")
    batch_sha = hashlib.sha256(batch_path.read_bytes()).hexdigest()
    return {"entries_hash": entries_hash, "root": root, "leaves": leaves}, batch_sha


def compare_zip_reproducibility(root: Path) -> tuple[bool, str, str]:
    if not root.exists():
        return True, "", ""
    with tempfile.TemporaryDirectory() as tmpdir:
        first = Path(tmpdir) / "first.zip"
        second = Path(tmpdir) / "second.zip"
        first_bytes = write_zip(root, first)
        second_bytes = write_zip(root, second)
    return first_bytes == second_bytes, hashlib.sha256(first_bytes).hexdigest(), hashlib.sha256(second_bytes).hexdigest()


def write_report(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, separators=(",", ":")), encoding="utf-8")


def main(argv: Iterable[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Check deterministic hashes for Sprint 7 batch")
    parser.add_argument("--batch", default=str(DEFAULT_BATCH))
    parser.add_argument("--out", default=str(DEFAULT_OUT))
    parser.add_argument("--dir", default=str(DEFAULT_DIR))
    parser.add_argument("--evidence-root", default="out")
    args = parser.parse_args(list(argv) if argv is not None else None)

    batch_path = Path(args.batch)
    out_path = Path(args.out)
    evidence_dir = Path(args.dir)
    evidence_root = Path(args.evidence_root)

    expected_hashes, expected_batch_sha = load_expected()
    actual_hashes, actual_batch_sha = compute_actual(batch_path)

    compare_payload = {
        "expected": expected_hashes,
        "actual": actual_hashes,
    }
    write_report(out_path, compare_payload)

    hashes_ok = (
        actual_hashes["entries_hash"] == expected_hashes.get("entries_hash")
        and actual_hashes["root"] == expected_hashes.get("root")
        and actual_hashes.get("leaves") == expected_hashes.get("leaves")
        and actual_batch_sha == expected_batch_sha
    )

    zip_equal, zip_sha_first, zip_sha_second = compare_zip_reproducibility(evidence_root)

    hash_match_payload = {
        "ok": hashes_ok and zip_equal,
        "byte_equal": hashes_ok,
        "zip_equal": zip_equal,
        "hash_match": hashes_ok,
    }
    write_report(evidence_dir / "hash_match.json", hash_match_payload)

    zip_compare_payload = {
        "ok": zip_equal,
        "zip_equal": zip_equal,
        "sha256_first": zip_sha_first,
        "sha256_second": zip_sha_second,
    }
    write_report(evidence_dir / "zip_compare.json", zip_compare_payload)

    return 0 if hash_match_payload["ok"] else 60


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
