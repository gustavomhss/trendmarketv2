import json
import pytest

from scripts.crypto.sign_batch import (
    PRIVKEY_PATH,
    PUBKEY_PATH,
    SignBatchError,
    sign_batch,
)
from scripts.crypto.verify_batch import VerificationError, verify_signature


@pytest.fixture()
def sample_batch(tmp_path):
    batch = {
        "entries_hash": "a" * 64,
        "root": "b" * 64,
        "schema_version": "1",
        "created_at": "2025-01-01T00:00:00Z",
    }
    batch_path = tmp_path / "batch.json"
    batch_path.write_text(json.dumps(batch, separators=(",", ":"), sort_keys=True))
    return batch_path, batch


@pytest.fixture(autouse=True)
def isolate_paths(monkeypatch, tmp_path):
    sig_path = tmp_path / "signature.sig.json"
    monkeypatch.setattr("scripts.crypto.sign_batch.SIGNATURE_PATH", sig_path)
    monkeypatch.setattr("scripts.crypto.sign_batch.BATCH_PATH", tmp_path / "batch.json")
    monkeypatch.setattr("scripts.crypto.verify_batch.BATCH_PATH", tmp_path / "batch.json")
    yield


def test_sign_and_verify_roundtrip(sample_batch, tmp_path):
    batch_path, batch = sample_batch
    signature_path = tmp_path / "signed.sig.json"
    result_path = sign_batch(
        batch_path,
        out_path=signature_path,
        privkey_path=PRIVKEY_PATH,
        pubkey_path=PUBKEY_PATH,
    )
    assert result_path == signature_path

    verify_result = verify_signature(
        batch_path,
        signature_path=signature_path,
        pubkey_path=PUBKEY_PATH,
    )
    assert verify_result["ok"] is True

    signed_doc = json.loads(signature_path.read_text())
    assert signed_doc["payload"] == batch
    assert verify_result["payload_sha256"] == signed_doc["payload_sha256"]


def test_sign_batch_requires_mandatory_fields(sample_batch):
    batch_path, batch = sample_batch
    batch_data = json.loads(batch_path.read_text())
    batch_data.pop("root")
    batch_path.write_text(json.dumps(batch_data))
    with pytest.raises(SignBatchError):
        sign_batch(batch_path)


def test_verify_detects_tampered_payload(sample_batch, tmp_path):
    batch_path, _ = sample_batch
    signature_path = sign_batch(batch_path, out_path=tmp_path / "sig.json")

    doc = json.loads(signature_path.read_text())
    doc["payload"]["root"] = "c" * 64
    signature_path.write_text(json.dumps(doc))

    with pytest.raises(VerificationError):
        verify_signature(batch_path, signature_path=signature_path)


def test_verify_rejects_domain_tag_override(sample_batch, tmp_path):
    batch_path, _ = sample_batch
    signature_path = sign_batch(batch_path, out_path=tmp_path / "sig.json")
    with pytest.raises(VerificationError):
        verify_signature(
            batch_path,
            signature_path=signature_path,
            domain_tag="tm.s7.batch.v1-alt",
        )
