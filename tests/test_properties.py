from __future__ import annotations

import json
from pathlib import Path

from scripts.det import check_determinism
from scripts.evidence import pack as evidence_pack
from scripts.merkle import append_only_guard
from scripts.merkle.merkle_build import build_merkle_tree
from scripts.normalizer.normalize_batch import Decimal4Encoder, build_batch_document, normalize_records

FIXTURE_JSON = Path("tests/fixtures/data/dataset-a.json")
NEG_LOG = Path("tests/fixtures/data/log-invalid-prev-root.jsonl")


def test_normalization_idempotent() -> None:
    first = normalize_records(FIXTURE_JSON)
    second = normalize_records(FIXTURE_JSON)
    assert first == second


def test_merkle_determinism(tmp_path: Path) -> None:
    records = normalize_records(FIXTURE_JSON)
    batch = build_batch_document(records)
    batch_path = tmp_path / "batch.json"
    batch_path.write_text(
        json.dumps(batch, cls=Decimal4Encoder, separators=(",", ":")),
        encoding="utf-8",
    )
    build_merkle_tree(batch_path, batch_path)
    first_root = json.loads(batch_path.read_text())['root']
    build_merkle_tree(batch_path, batch_path)
    second_root = json.loads(batch_path.read_text())['root']
    assert first_root == second_root


def test_append_only_guard_detects_violation(tmp_path: Path) -> None:
    batch_path = tmp_path / "batch.json"
    batch_path.write_text("{}", encoding="utf-8")
    log_path = tmp_path / "log.jsonl"
    log_path.write_text(NEG_LOG.read_text(encoding="utf-8"), encoding="utf-8")
    payload = append_only_guard.guard_append_only(
        append_only_guard.load_log(log_path),
        json.loads(batch_path.read_text()),
        batch_path.read_bytes(),
    )
    assert payload["ok"] is False
    assert payload["violations"] > 0


def test_pack_reproducible_zip(tmp_path: Path) -> None:
    root = tmp_path / "out"
    evidence_dir = root / "evidence" / "T4_tests"
    evidence_dir.mkdir(parents=True)
    artifact = evidence_dir / "pytest_report.json"
    artifact.write_text(json.dumps({"ok": True, "duration_ms": 1234}, separators=(",", ":")), encoding="utf-8")

    evidence_pack.generate_summaries(root)
    first_zip = tmp_path / "first.zip"
    second_zip = tmp_path / "second.zip"
    first_bytes = evidence_pack.write_zip(root, first_zip)
    second_bytes = evidence_pack.write_zip(root, second_zip)
    assert first_bytes == second_bytes

    sha_path = tmp_path / "sha.txt"
    evidence_pack.write_sha256(first_zip, sha_path)
    digest = sha_path.read_text(encoding="utf-8")
    assert len(digest) == 64
    assert all(ch in "0123456789abcdef" for ch in digest)


def test_check_determinism_matches_expected(tmp_path: Path) -> None:
    batch_path = tmp_path / "batch.json"
    records = normalize_records(FIXTURE_JSON)
    batch = build_batch_document(records)
    batch_path.write_text(
        json.dumps(batch, cls=Decimal4Encoder, separators=(",", ":")),
        encoding="utf-8",
    )
    build_merkle_tree(batch_path, batch_path)

    expected_hashes, expected_batch_sha = check_determinism.load_expected()
    actual_hashes, actual_batch_sha = check_determinism.compute_actual(batch_path)

    assert actual_hashes["entries_hash"] == expected_hashes["entries_hash"]
    assert actual_hashes["root"] == expected_hashes["root"]
    assert actual_hashes["leaves"] == expected_hashes["leaves"]
    assert actual_batch_sha == expected_batch_sha
