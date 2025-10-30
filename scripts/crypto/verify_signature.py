#!/usr/bin/env python3
"""Verify oracle batch signatures against the keystore."""
from __future__ import annotations

import argparse
import base64
import binascii
import json
import sys
from datetime import datetime, timedelta, timezone
from pathlib import Path
from typing import Any, Dict

sys.path.append(str(Path(__file__).resolve().parents[2]))
from tools.crypto import ed25519

DEFAULT_SIGNATURE_PATH = Path("out/evidence/S7_event_model/signature.json")
DEFAULT_KEYSTORE_PATH = Path("tools/crypto/keystore.json")
DEFAULT_BATCH_PATH = Path("out/evidence/S7_event_model/batch_latest.json")


class VerificationError(RuntimeError):
    pass


def _parse_time(value: str) -> datetime:
    return datetime.fromisoformat(value.replace("Z", "+00:00")).astimezone(timezone.utc)


def _load_json(path: Path) -> Dict[str, Any]:
    with path.open("r", encoding="utf-8") as handle:
        data = json.load(handle)
    if not isinstance(data, dict):
        raise VerificationError(f"{path} must contain a JSON object")
    return data


def _validate_key_window(key: Dict[str, Any], *, now: datetime) -> None:
    created = _parse_time(key["created_at"])
    not_after = _parse_time(key["not_after"])
    status = key.get("status")
    window_end = not_after
    if status == "retiring":
        window_end = not_after + timedelta(days=7)
    if not (created <= now <= window_end):
        raise VerificationError("Key is outside its validity window")
    if (not_after - created).days > 90:
        raise VerificationError("Key violates rotation policy ( >90 days )")


def _resolve_key(keystore: Dict[str, Any], kid: str) -> Dict[str, Any]:
    keys = keystore.get("keys")
    if not isinstance(keys, list):
        raise VerificationError("Invalid keystore structure")
    for key in keys:
        if key.get("kid") == kid:
            return key
    raise VerificationError(f"Key {kid} not found in keystore")


def verify_signature(signature_path: Path, keystore_path: Path, batch_path: Path) -> None:
    now = datetime.now(timezone.utc)
    signature = _load_json(signature_path)
    keystore = _load_json(keystore_path)
    batch = _load_json(batch_path)

    kid = signature.get("kid")
    if not isinstance(kid, str):
        raise VerificationError("Signature missing kid")
    key = _resolve_key(keystore, kid)
    _validate_key_window(key, now=now)

    if key.get("alg") != "Ed25519" or signature.get("alg") != "Ed25519":
        raise VerificationError("Algorithm mismatch; expected Ed25519")

    sig_b64 = signature.get("sig")
    if not isinstance(sig_b64, str):
        raise VerificationError("Signature payload missing 'sig'")
    try:
        sig = base64.b64decode(sig_b64)
    except (ValueError, binascii.Error) as exc:
        raise VerificationError("Signature is not valid base64") from exc

    pub_b64 = key.get("pubkey")
    if not isinstance(pub_b64, str):
        raise VerificationError("Key missing pubkey")
    try:
        pub = base64.b64decode(pub_b64)
    except (ValueError, binascii.Error) as exc:
        raise VerificationError("Public key is not valid base64") from exc

    message = f"{batch['merkle_root']}|{batch['batch_ts']}".encode("utf-8")
    if not ed25519.verify(sig, message, pub):
        raise VerificationError("Signature verification failed")


def main() -> None:
    parser = argparse.ArgumentParser(description="Verify oracle batch signatures")
    parser.add_argument("--signature", type=Path, default=DEFAULT_SIGNATURE_PATH)
    parser.add_argument("--keystore", type=Path, default=DEFAULT_KEYSTORE_PATH)
    parser.add_argument("--batch", type=Path, default=DEFAULT_BATCH_PATH)
    args = parser.parse_args()
    try:
        verify_signature(args.signature, args.keystore, args.batch)
    except VerificationError as exc:
        raise SystemExit(str(exc)) from exc


if __name__ == "__main__":
    main()
