from __future__ import annotations

import json
from pathlib import Path

import pytest

from scripts.crypto import sign_batch, verify_batch
from scripts.merkle.merkle_build import build_merkle_tree
from scripts.normalizer.normalize_batch import Decimal4Encoder, build_batch_document, normalize_records

FIXTURE_JSON = Path("tests/fixtures/data/dataset-a.json")


def build_batch(tmp_path: Path) -> Path:
    records = normalize_records(FIXTURE_JSON)
    batch = build_batch_document(records)
    batch_path = tmp_path / "batch.json"
    batch_path.write_text(
        json.dumps(batch, cls=Decimal4Encoder, separators=(",", ":")),
        encoding="utf-8",
    )
    build_merkle_tree(batch_path, batch_path)
    return batch_path


def test_sign_and_verify_round_trip(tmp_path: Path) -> None:
    batch_path = build_batch(tmp_path)
    signature_path = tmp_path / "batch.sig.json"
    sign_batch.sign_batch(batch_path, out_path=signature_path)
    result = verify_batch.verify_signature(batch_path, signature_path=signature_path)
    assert result["ok"] is True
    assert result["batch_sha256"]


def test_verify_domain_tag_mismatch(tmp_path: Path) -> None:
    batch_path = build_batch(tmp_path)
    signature_path = tmp_path / "batch.sig.json"
    sign_batch.sign_batch(batch_path, out_path=signature_path)
    with pytest.raises(verify_batch.VerificationError):
        verify_batch.verify_signature(batch_path, signature_path=signature_path, domain_tag="tm.s7.batch.vX")
