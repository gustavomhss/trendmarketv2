#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import base64
import json
import hashlib
from datetime import datetime, timezone
from typing import Any

from nacl import signing, exceptions as nacl_exc


class VerificationError(Exception):
    """Raised when a signature or keystore entry cannot be validated."""


def _read_json(path: Path) -> Any:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        raise VerificationError(f"missing file: {path}") from exc
    except json.JSONDecodeError as exc:
        raise VerificationError(f"invalid JSON: {path}") from exc


def _parse_time(value: str) -> datetime:
    if value.endswith("Z"):
        value = value[:-1] + "+00:00"
    dt = datetime.fromisoformat(value)
    if dt.tzinfo is None:
        dt = dt.replace(tzinfo=timezone.utc)
    return dt.astimezone(timezone.utc)


def _decode_b64(value: str, field: str) -> bytes:
    try:
        return base64.b64decode(value, validate=True)
    except Exception as exc:  # noqa: BLE001
        raise VerificationError(f"invalid base64 for {field}") from exc


def _keystore_entry(keys: list[Any], pubkey_b64: str) -> dict[str, Any]:
    for entry in keys:
        if isinstance(entry, dict) and entry.get("pubkey") == pubkey_b64:
            return entry
    raise VerificationError("public key not present in keystore")


def _validity_window(entry: dict[str, Any]) -> tuple[datetime, datetime]:
    not_before_val = entry.get("not_before") or entry.get("valid_from")
    if not isinstance(not_before_val, str):
        raise VerificationError("keystore entry missing validity window")
    not_before_dt = _parse_time(not_before_val)

    expires_candidates = []
    for key in ("expires_at", "not_after", "valid_until"):
        value = entry.get(key)
        if isinstance(value, str):
            expires_candidates.append(_parse_time(value))
    if not expires_candidates:
        raise VerificationError("keystore entry missing validity window")
    expires_dt = min(expires_candidates)
    return not_before_dt, expires_dt


def verify_signature(signature_path: Path, keystore_path: Path, batch_path: Path) -> bool:
    signature_data = _read_json(signature_path)
    if not isinstance(signature_data, dict):
        raise VerificationError("signature payload must be an object")

    algo = signature_data.get("algo")
    if algo != "ed25519":
        raise VerificationError("unsupported signature algorithm")

    pubkey_b64 = signature_data.get("pubkey")
    signature_b64 = signature_data.get("sig") or signature_data.get("signature")
    if not isinstance(pubkey_b64, str) or not isinstance(signature_b64, str):
        raise VerificationError("signature payload missing fields")

    pubkey = _decode_b64(pubkey_b64, "pubkey")
    signature = _decode_b64(signature_b64, "signature")

    batch_bytes = batch_path.read_bytes()
    batch_sha = signature_data.get("batch_sha256")
    if batch_sha is not None:
        if not isinstance(batch_sha, str):
            raise VerificationError("batch_sha256 must be a string if present")
        computed_sha = hashlib.sha256(batch_bytes).hexdigest()
        if computed_sha != batch_sha:
            raise VerificationError("batch_sha256 mismatch")

    keystore_data = _read_json(keystore_path)
    keys = keystore_data.get("keys") if isinstance(keystore_data, dict) else None
    if not isinstance(keys, list):
        raise VerificationError("keystore format invalid")

    entry = _keystore_entry(keys, pubkey_b64)
    not_before_dt, expires_dt = _validity_window(entry)

    now = datetime.now(timezone.utc)
    if not (not_before_dt <= now <= expires_dt):
        raise VerificationError("keystore entry outside validity window")

    verify_key = signing.VerifyKey(pubkey)
    try:
        verify_key.verify(batch_bytes, signature)
    except nacl_exc.BadSignatureError as exc:
        raise VerificationError("invalid signature") from exc

    return True


def main() -> None:
    raise SystemExit("verify_signature CLI disabled in this context")


if __name__ == "__main__":
    main()
