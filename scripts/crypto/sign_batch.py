#!/usr/bin/env python3
"""Sign the latest oracle batch using the active Ed25519 key."""
from __future__ import annotations

import argparse
import base64
import binascii
import json
import os
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, List

sys.path.append(str(Path(__file__).resolve().parents[2]))
from tools.crypto import ed25519

DEFAULT_BATCH_PATH = Path("out/evidence/S7_event_model/batch_latest.json")
DEFAULT_KEYSTORE_PATH = Path("tools/crypto/keystore.json")
SIGNATURE_PATH = Path("out/evidence/S7_event_model/signature.json")


class SigningError(RuntimeError):
    pass


def _parse_time(value: str) -> datetime:
    return datetime.fromisoformat(value.replace("Z", "+00:00")).astimezone(timezone.utc)


def _load_keystore(path: Path) -> Dict[str, Any]:
    with path.open("r", encoding="utf-8") as handle:
        return json.load(handle)


def _select_active_key(keys: List[Dict[str, Any]], *, now: datetime) -> Dict[str, Any]:
    active_keys = []
    for key in keys:
        if key.get("status") != "active":
            continue
        created = _parse_time(key["created_at"])
        not_after = _parse_time(key["not_after"])
        if not (created <= now <= not_after):
            continue
        if (not_after - created).days > 90:
            raise SigningError("Active key violates 90 day rotation policy")
        active_keys.append((created, key))
    if not active_keys:
        raise SigningError("No active key available in keystore")
    active_keys.sort(key=lambda item: item[0], reverse=True)
    return active_keys[0][1]


def _load_seed_for_key(kid: str) -> bytes:
    env_name = f"ORACLE_ED25519_SEED_{kid.upper()}"
    fallback = os.getenv("ORACLE_ED25519_SEED")
    encoded = os.getenv(env_name, fallback)
    if not encoded:
        raise SigningError(f"Missing seed for key {kid}. Set {env_name} or ORACLE_ED25519_SEED")
    try:
        seed = base64.b64decode(encoded)
    except (ValueError, binascii.Error) as exc:
        raise SigningError("Seed must be base64 encoded") from exc
    if len(seed) != 32:
        raise SigningError("Seed must be 32 bytes")
    return seed


def _build_message(batch: Dict[str, Any]) -> bytes:
    merkle_root = batch.get("merkle_root")
    batch_ts = batch.get("batch_ts")
    if not isinstance(merkle_root, str) or not isinstance(batch_ts, str):
        raise SigningError("Batch file missing merkle_root or batch_ts")
    return f"{merkle_root}|{batch_ts}".encode("utf-8")


def sign_batch(batch_path: Path, keystore_path: Path) -> Dict[str, Any]:
    now = datetime.now(timezone.utc)
    keystore = _load_keystore(keystore_path)
    keys = keystore.get("keys")
    if not isinstance(keys, list):
        raise SigningError("Keystore must contain a list of keys")
    key = _select_active_key(keys, now=now)
    kid = key["kid"]
    seed = _load_seed_for_key(kid)
    public_b64 = key["pubkey"]
    try:
        public = base64.b64decode(public_b64)
    except (ValueError, binascii.Error) as exc:
        raise SigningError("Invalid base64 public key") from exc
    if len(public) != 32:
        raise SigningError("Public key must be 32 bytes")

    with batch_path.open("r", encoding="utf-8") as handle:
        batch = json.load(handle)

    message = _build_message(batch)
    signature = ed25519.sign(message, seed, public)
    signature_b64 = base64.b64encode(signature).decode("utf-8")

    record = {
        "kid": kid,
        "alg": key["alg"],
        "sig": signature_b64,
        "merkle_root": batch["merkle_root"],
        "ts": batch["batch_ts"],
    }

    SIGNATURE_PATH.parent.mkdir(parents=True, exist_ok=True)
    with SIGNATURE_PATH.open("w", encoding="utf-8") as handle:
        json.dump(record, handle, ensure_ascii=False, indent=2)
    return record


def main() -> None:
    parser = argparse.ArgumentParser(description="Sign oracle batch evidence")
    parser.add_argument("--batch", type=Path, default=DEFAULT_BATCH_PATH)
    parser.add_argument("--keystore", type=Path, default=DEFAULT_KEYSTORE_PATH)
    args = parser.parse_args()
    try:
        sign_batch(args.batch, args.keystore)
    except SigningError as exc:
        raise SystemExit(str(exc)) from exc


if __name__ == "__main__":
    main()
