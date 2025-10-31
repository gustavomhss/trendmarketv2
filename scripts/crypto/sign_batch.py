#!/usr/bin/env python3
from __future__ import annotations

from typing import Union
from pathlib import Path
import os
import json
import base64
import hashlib

from nacl import signing

PathLike = Union[str, Path]

SIGNATURE_PATH: Path = Path("out/evidence/S7_event_model/batch.signature.json")


def _ensure_dir(p: Path) -> None:
    p.mkdir(parents=True, exist_ok=True)


def _decode_seed(seed_b64: str) -> bytes:
    try:
        seed = base64.b64decode(seed_b64, validate=True)
    except Exception as exc:  # noqa: BLE001
        raise RuntimeError("Invalid ORACLE_ED25519_SEED base64") from exc
    if len(seed) != 32:
        raise RuntimeError("ORACLE_ED25519_SEED must decode to 32 bytes")
    return seed


def _load_seed() -> bytes:
    seed_b64 = os.environ.get("ORACLE_ED25519_SEED")
    if not seed_b64:
        raise RuntimeError("Missing ORACLE_ED25519_SEED environment variable")
    return _decode_seed(seed_b64)


def _keystore_entry(pubkey_b64: str) -> dict[str, str]:
    expires = "9999-12-31T23:59:59Z"
    return {
        "pubkey": pubkey_b64,
        "not_before": "1970-01-01T00:00:00Z",
        "expires_at": expires,
        "not_after": expires,
    }


def _merge_entry(entry: dict[str, object], pubkey_b64: str) -> dict[str, object]:
    merged = dict(entry)
    merged.update(_keystore_entry(pubkey_b64))
    return merged


def _ensure_keystore(keystore_path: Path, pubkey_b64: str) -> None:
    _ensure_dir(keystore_path.parent)
    loaded: dict[str, object] = {}
    keys: list[dict[str, object]] | None = None
    if keystore_path.exists():
        try:
            existing = json.loads(keystore_path.read_text(encoding="utf-8"))
            if isinstance(existing, dict):
                loaded = dict(existing)
                maybe_keys = existing.get("keys")
                if isinstance(maybe_keys, list):
                    keys = [entry for entry in maybe_keys if isinstance(entry, dict)]
        except json.JSONDecodeError:
            loaded = {}
    if keys is None:
        keys = []
    others: list[dict[str, object]] = []
    our_entry: dict[str, object] | None = None
    for entry in keys:
        if entry.get("pubkey") == pubkey_b64 and our_entry is None:
            our_entry = _merge_entry(entry, pubkey_b64)
        else:
            others.append(entry)
    if our_entry is None:
        our_entry = _keystore_entry(pubkey_b64)
    loaded["keys"] = [our_entry, *others]
    keystore_path.write_text(json.dumps(loaded, indent=2) + "\n", encoding="utf-8")


def sign_batch(batch_path: PathLike, keystore_path: PathLike) -> Path:
    batch_file = Path(batch_path)
    batch_bytes = batch_file.read_bytes()
    batch_sha = hashlib.sha256(batch_bytes).hexdigest()

    seed = _load_seed()
    signer = signing.SigningKey(seed)
    verify_key = signer.verify_key
    pubkey_b64 = base64.b64encode(bytes(verify_key)).decode("ascii")
    signature = signer.sign(batch_bytes).signature
    signature_b64 = base64.b64encode(signature).decode("ascii")

    payload = {
        "algo": "ed25519",
        "pubkey": pubkey_b64,
        "signature": signature_b64,
        "sig": signature_b64,
        "batch_sha256": batch_sha,
    }

    _ensure_dir(SIGNATURE_PATH.parent)
    SIGNATURE_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")

    _ensure_keystore(Path(keystore_path), pubkey_b64)

    return SIGNATURE_PATH


def main() -> None:
    raise SystemExit("sign_batch CLI disabled in this context")


if __name__ == "__main__":
    main()
