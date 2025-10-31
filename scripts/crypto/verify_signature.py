#!/usr/bin/env python3
from __future__ import annotations

import base64
import json
from datetime import datetime, timezone
from hashlib import sha256
from pathlib import Path
from typing import Any, Dict

try:  # pragma: no cover - fallback when PyNaCl is not installed
    from nacl import exceptions as nacl_exc, signing  # type: ignore
except ModuleNotFoundError:  # pragma: no cover - exercised in CI image without PyNaCl
    from tools.crypto import ed25519 as _ed25519

    class _BadSignatureError(Exception):
        pass

    class _VerifyKey:
        def __init__(self, key: bytes) -> None:
            if len(key) != 32:
                raise ValueError("Ed25519 public key must be 32 bytes")
            self._key = key

        def verify(self, message: bytes, signature: bytes) -> bytes:
            if not _ed25519.verify(signature, message, self._key):
                raise _BadSignatureError("invalid Ed25519 signature")
            return message

    class _SigningModule:
        VerifyKey = _VerifyKey

    class _ExceptionsModule:
        BadSignatureError = _BadSignatureError

    signing = _SigningModule()  # type: ignore
    nacl_exc = _ExceptionsModule()  # type: ignore


class VerificationError(Exception):
    pass


def _read_json(path: Path) -> Dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _parse_iso8601(value: str) -> datetime:
    candidate = value
    if candidate.endswith("Z"):
        candidate = candidate[:-1] + "+00:00"
    dt = datetime.fromisoformat(candidate)
    if dt.tzinfo is None:
        dt = dt.replace(tzinfo=timezone.utc)
    else:
        dt = dt.astimezone(timezone.utc)
    return dt


def _extract_public_key(entry: Dict[str, Any]) -> bytes:
    pubkey_b64 = entry.get("pubkey") or entry.get("public_key") or entry.get("public_key_b64")
    if not isinstance(pubkey_b64, str):
        raise VerificationError("keystore entry missing public key")
    return base64.b64decode(pubkey_b64, validate=True)


def _find_key(keystore: Dict[str, Any], key_id: str) -> Dict[str, Any]:
    keys = keystore.get("keys")
    if not isinstance(keys, list):
        raise VerificationError("keystore missing keys list")
    for entry in keys:
        if isinstance(entry, dict) and entry.get("kid") == key_id:
            return entry
    raise VerificationError(f"key_id {key_id} not found in keystore")


def verify_signature(signature_path: Path, keystore_path: Path, batch_path: Path) -> None:
    signature_doc = _read_json(signature_path)
    keystore_doc = _read_json(keystore_path)

    algorithm = signature_doc.get("algorithm")
    if algorithm and str(algorithm).lower() != "ed25519":
        raise VerificationError("unsupported signature algorithm")

    key_id = signature_doc.get("key_id")
    if not isinstance(key_id, str) or not key_id:
        raise VerificationError("signature missing key_id")

    claimed_pub_b64 = signature_doc.get("public_key_b64")
    signature_primary = signature_doc.get("signature_b64")
    signature_legacy = signature_doc.get("sig")
    if signature_primary is None and signature_legacy is None:
        raise VerificationError("signature payload missing signature data")
    if signature_primary is None:
        signature_b64 = signature_legacy
    else:
        if signature_legacy is not None and signature_primary != signature_legacy:
            raise VerificationError("signature mismatch between fields")
        signature_b64 = signature_primary
    if not isinstance(signature_b64, str):
        raise VerificationError("signature payload missing signature data")

    signed_at_raw = signature_doc.get("signed_at")
    if not isinstance(signed_at_raw, str):
        raise VerificationError("signature missing signed_at timestamp")
    signed_at = _parse_iso8601(signed_at_raw)

    recorded_hash = signature_doc.get("batch_sha256")
    if not isinstance(recorded_hash, str):
        raise VerificationError("signature missing batch_sha256")

    batch_bytes = batch_path.read_bytes()
    computed_hash = sha256(batch_bytes).hexdigest()
    if computed_hash != recorded_hash:
        raise VerificationError("batch_sha256 mismatch")

    key_entry = _find_key(keystore_doc, key_id)
    not_after_raw = key_entry.get("not_after")
    if isinstance(not_after_raw, str):
        not_after = _parse_iso8601(not_after_raw)
        if signed_at > not_after:
            raise VerificationError("key expired for signed_at timestamp")

    expected_public_key = _extract_public_key(key_entry)

    if claimed_pub_b64 is not None:
        if not isinstance(claimed_pub_b64, str):
            raise VerificationError("public_key_b64 must be a base64 string")
        claimed_public_key = base64.b64decode(claimed_pub_b64, validate=True)
        if claimed_public_key != expected_public_key:
            raise VerificationError("public key mismatch between signature and keystore")

    signature_bytes = base64.b64decode(signature_b64, validate=True)

    verify_key = signing.VerifyKey(expected_public_key)
    try:
        verify_key.verify(batch_bytes, signature_bytes)
    except nacl_exc.BadSignatureError as exc:  # pragma: no cover - defensive
        raise VerificationError("invalid Ed25519 signature") from exc

    # success -> return None
    return None
