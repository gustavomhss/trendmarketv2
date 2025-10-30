#!/usr/bin/env python3
from __future__ import annotations

import base64
import json
import os
import re
import sys
from pathlib import Path

from nacl import signing

KEY_ID = os.environ.get("ORACLE_SIGNING_KEY_ID", "s7-active-20251001")

def _env_name_for_key(key_id: str) -> str:
    safe = re.sub(r"[^A-Za-z0-9_]", "_", key_id.upper())
    return f"ORACLE_ED25519_SEED_{safe}"

def _get_seed_b64() -> str | None:
    # específico por KEY_ID (underscore) ou genérico
    return os.environ.get(_env_name_for_key(KEY_ID)) or os.environ.get("ORACLE_ED25519_SEED")

def _decode_seed(seed_b64: str) -> bytes:
    raw = base64.b64decode(seed_b64, validate=True)
    if len(raw) != 32:
        print(f"[sign] seed must be 32 bytes after base64; got {len(raw)}", file=sys.stderr)
        sys.exit(1)
    return raw

def _choose_batch_files() -> tuple[Path, Path]:
    """Retorna (batch_json, batch_sig) canônicos em out/evidence/S7_event_model/"""
    root = Path("out/evidence/S7_event_model")
    root.mkdir(parents=True, exist_ok=True)
    # Preferir batch.json/batch.sig se já existirem
    bj, bs = root / "batch.json", root / "batch.sig"
    if bj.exists():
        return bj, bs
    # Caso contrário, escolha o .json mais novo no diretório
    candidates = sorted(root.glob("*.json"))
    if not candidates:
        print("[sign] no batch JSON found in out/evidence/S7_event_model", file=sys.stderr)
        sys.exit(1)
    latest = candidates[-1]
    # Canonicalize como batch.json + batch.sig (cópia)
    bj.write_bytes(latest.read_bytes())
    return bj, bs

def main() -> None:
    seed_b64 = _get_seed_b64()
    if not seed_b64:
        print(
            f"Missing seed for key {KEY_ID}. Set {_env_name_for_key(KEY_ID)} or ORACLE_ED25519_SEED",
            file=sys.stderr,
        )
        sys.exit(1)
    seed = _decode_seed(seed_b64)
    signer = signing.SigningKey(seed)
    verify_key = signer.verify_key
    pub_b64 = base64.b64encode(bytes(verify_key)).decode()

    batch_json, batch_sig = _choose_batch_files()
    data = batch_json.read_bytes()
    signature = signer.sign(data).signature  # 64 bytes
    batch_sig.write_bytes(signature)

    # Emitir pubkey.json canônico
    pubmeta = {
        "alg": "Ed25519",
        "key_id": KEY_ID,
        "public_key_b64": pub_b64,
    }
    (batch_json.parent / "pubkey.json").write_text(json.dumps(pubmeta, indent=2), encoding="utf-8")

    print(f"[sign] wrote {batch_sig} and pubkey.json for {batch_json.name}")

if __name__ == "__main__":
    main()
