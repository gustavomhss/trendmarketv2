from __future__ import annotations

import base64
import json
from datetime import datetime, timezone
from pathlib import Path

import pytest

from scripts.crypto.sign_batch import sign_batch
from scripts.crypto.verify_signature import VerificationError, verify_signature
from services.oracle.normalizer.merkle_append_only import write_batch
from services.oracle.normalizer.normalizer import build_event

SEED_B64 = "YjVJzNqMrMo6vdEAHj0AVMSn7UvBcQDzXagHgN5KVPg="
FIXED_NOW = datetime(2025, 10, 29, 19, 10, tzinfo=timezone.utc)


@pytest.fixture()
def temp_batch_dir(tmp_path, monkeypatch):
    monkeypatch.setattr("services.oracle.normalizer.merkle_append_only.BATCH_DIR", tmp_path)
    monkeypatch.setattr("scripts.crypto.sign_batch.SIGNATURE_PATH", tmp_path / "signature.json")
    return tmp_path


def _build_sample_events() -> list[dict[str, object]]:
    base = {
        "lang": "pt",
        "category": "mercado",
        "source": "operador",
        "observed_at": "2025-10-29T18:59:00Z",
        "payload": {"valor": 1},
    }
    events = []
    for idx in range(3):
        raw = dict(base)
        raw["title"] = f"evento {idx}"
        events.append(dict(build_event(raw, now=FIXED_NOW)))
    return events


def test_sign_and_verify_roundtrip(temp_batch_dir, monkeypatch):
    events = _build_sample_events()
    write_batch(events, batch_ts=FIXED_NOW)
    monkeypatch.setenv("ORACLE_ED25519_SEED", SEED_B64)
    batch_path = temp_batch_dir / "batch_latest.json"
    signature_path = temp_batch_dir / "signature.json"
    sign_batch(batch_path, Path("tools/crypto/keystore.json"))
    verify_signature(signature_path, Path("tools/crypto/keystore.json"), batch_path)


def test_signature_fails_on_tamper(temp_batch_dir, monkeypatch):
    events = _build_sample_events()
    write_batch(events, batch_ts=FIXED_NOW)
    monkeypatch.setenv("ORACLE_ED25519_SEED", SEED_B64)
    batch_path = temp_batch_dir / "batch_latest.json"
    signature_path = temp_batch_dir / "signature.json"
    sign_batch(batch_path, Path("tools/crypto/keystore.json"))
    with signature_path.open("r", encoding="utf-8") as handle:
        data = json.load(handle)
    sig_bytes = bytearray(base64.b64decode(data["sig"]))
    sig_bytes[0] ^= 0x01
    data["sig"] = base64.b64encode(bytes(sig_bytes)).decode()
    with signature_path.open("w", encoding="utf-8") as handle:
        json.dump(data, handle)
    with pytest.raises(VerificationError):
        verify_signature(signature_path, Path("tools/crypto/keystore.json"), batch_path)


def test_expired_key_rejected(temp_batch_dir, monkeypatch, tmp_path):
    events = _build_sample_events()
    write_batch(events, batch_ts=FIXED_NOW)
    monkeypatch.setenv("ORACLE_ED25519_SEED", SEED_B64)
    batch_path = temp_batch_dir / "batch_latest.json"
    signature_path = temp_batch_dir / "signature.json"
    sign_batch(batch_path, Path("tools/crypto/keystore.json"))

    keystore_data = json.loads(Path("tools/crypto/keystore.json").read_text())
    keystore_data["keys"][0]["not_after"] = "2025-09-01T00:00:00Z"
    expired_path = tmp_path / "keystore_expired.json"
    expired_path.write_text(json.dumps(keystore_data))

    with pytest.raises(VerificationError):
        verify_signature(signature_path, expired_path, batch_path)
