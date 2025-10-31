#!/usr/bin/env python3
from __future__ import annotations

import base64
import json
import os
from datetime import datetime, timezone
from hashlib import sha256
from pathlib import Path
from typing import Any, Dict, Optional

try:  # pragma: no cover - fallback when PyNaCl is unavailable
    from nacl import signing  # type: ignore
except ModuleNotFoundError:  # pragma: no cover - exercised in CI image without PyNaCl
    from tools.crypto import ed25519 as _ed25519

    class _SignedMessage:
        def __init__(self, signature: bytes) -> None:
            self.signature = signature

    class _VerifyKey:
        def __init__(self, key: bytes) -> None:
            if len(key) != 32:
                raise ValueError("Ed25519 public key must be 32 bytes")
            self._key = key

        def verify(self, message: bytes, signature: bytes) -> bytes:
            if not _ed25519.verify(signature, message, self._key):
                raise ValueError("invalid signature")
            return message

        def __bytes__(self) -> bytes:
            return self._key

    class _SigningKey:
        def __init__(self, seed: bytes) -> None:
            if len(seed) != 32:
                raise ValueError("Ed25519 seed must be 32 bytes")
            self._seed = seed
            self.verify_key = _VerifyKey(_ed25519.public_key(seed))

        def sign(self, message: bytes) -> _SignedMessage:
            signature = _ed25519.sign(message, self._seed, bytes(self.verify_key))
            return _SignedMessage(signature)

    class _SigningModule:
        SigningKey = _SigningKey
        VerifyKey = _VerifyKey

    signing = _SigningModule()  # type: ignore

SIGNATURE_PATH = Path("out/evidence/S7_event_model/signature.json")


def _ensure_dir(path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)


def _load_json(path: Path) -> Dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _decode_seed(seed_b64: str) -> bytes:
    raw = base64.b64decode(seed_b64, validate=True)
    if len(raw) != 32:
        raise ValueError("Ed25519 seed must be 32 bytes after base64 decoding")
    return raw


def _active_key_entry(keystore: Dict[str, Any]) -> Dict[str, Any]:
    keys = keystore.get("keys")
    if not isinstance(keys, list):
        raise ValueError("keystore missing 'keys' list")

    for entry in keys:
        if isinstance(entry, dict) and entry.get("status") == "active":
            return entry

    for entry in keys:
        if isinstance(entry, dict):
            return entry

    raise ValueError("keystore does not contain usable keys")


def _seed_from_keystore(entry: Dict[str, Any]) -> Optional[str]:
    for field in ("seed", "seed_b64", "secret_key", "private_key", "sk"):
        value = entry.get(field)
        if isinstance(value, str):
            return value
    return None


def _now_iso_z() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def sign_batch(batch_path: Path, keystore_path: Path, signature_path: Optional[Path] = None) -> Path:
    keystore_data = _load_json(keystore_path)
    key_entry = _active_key_entry(keystore_data)
    key_id = key_entry.get("kid")
    if not isinstance(key_id, str) or not key_id:
        raise ValueError("active key is missing 'kid'")

    seed_b64 = os.environ.get("ORACLE_ED25519_SEED")
    if not seed_b64:
        seed_b64 = _seed_from_keystore(key_entry)
    if not seed_b64:
        raise RuntimeError("missing Ed25519 seed: provide ORACLE_ED25519_SEED or keystore seed entry")

    seed = _decode_seed(seed_b64)
    signing_key = signing.SigningKey(seed)
    public_key = signing_key.verify_key
    public_key_b64 = base64.b64encode(bytes(public_key)).decode("utf-8")

    keystore_pub = key_entry.get("pubkey") or key_entry.get("public_key")
    if isinstance(keystore_pub, str):
        expected_pub = base64.b64decode(keystore_pub, validate=True)
        if expected_pub != bytes(public_key):
            raise RuntimeError("provided seed does not match keystore public key")

    target_path = signature_path or SIGNATURE_PATH
    _ensure_dir(target_path)

    batch_bytes = batch_path.read_bytes()
    signature = signing_key.sign(batch_bytes).signature
    signature_b64 = base64.b64encode(signature).decode("utf-8")
    batch_hash = sha256(batch_bytes).hexdigest()

    payload = {
        "algorithm": "ed25519",
        "key_id": key_id,
        "public_key_b64": public_key_b64,
        "batch_sha256": batch_hash,
        "signature_b64": signature_b64,
        "sig": signature_b64,
        "signed_at": _now_iso_z(),
    }

    target_path.write_text(json.dumps(payload, ensure_ascii=False, sort_keys=True), encoding="utf-8")
    return target_path
