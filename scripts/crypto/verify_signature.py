#!/usr/bin/env python3
from __future__ import annotations

import base64
import json
import os
import sys
from pathlib import Path
from typing import Optional

from nacl import exceptions as nacl_exc
from nacl import signing

KEY_ID = os.environ.get("ORACLE_SIGNING_KEY_ID", "s7-active-20251001")

def _load_pub_from_pubmeta(dir_: Path) -> Optional[bytes]:
    p = dir_ / "pubkey.json"
    if not p.exists():
        return None
    meta = json.loads(p.read_text(encoding="utf-8"))
    b64 = meta.get("public_key_b64")
    if not isinstance(b64, str):
        return None
    return base64.b64decode(b64, validate=True)

def _choose_batch_files() -> tuple[Path, Path]:
    root = Path("out/evidence/S7_event_model")
    bj, bs = root / "batch.json", root / "batch.sig"
    if not bj.exists():
        # escolhe o mais novo
        js = sorted(root.glob("*.json"))
        if not js:
            print("[verify] no batch JSON found to verify", file=sys.stderr)
            sys.exit(1)
        bj = js[-1]
    if not bs.exists():
        # tenta sig de mesmo stem
        cand = bj.with_suffix(".sig")
        if cand.exists():
            bs = cand
        else:
            print("[verify] no signature file found for batch", file=sys.stderr)
            sys.exit(1)
    return bj, bs

def _load_pub_from_env() -> Optional[bytes]:
    val = os.environ.get("ORACLE_ED25519_PUB")
    if not val:
        return None
    return base64.b64decode(val, validate=True)

def _derive_pub_from_seed() -> Optional[bytes]:
    seed_b64 = os.environ.get("ORACLE_ED25519_SEED")
    if not seed_b64:
        return None
    raw = base64.b64decode(seed_b64, validate=True)
    if len(raw) != 32:
        print("[verify] ORACLE_ED25519_SEED is not 32 bytes after base64", file=sys.stderr)
        sys.exit(1)
    return bytes(signing.SigningKey(raw).verify_key)

def main() -> None:
    bj, bs = _choose_batch_files()
    pub: Optional[bytes] = None

    # 1) pubkey.json canônico
    pub = _load_pub_from_pubmeta(bj.parent)
    # 2) env ORACLE_ED25519_PUB (base64)
    if pub is None:
        pub = _load_pub_from_env()
    # 3) derivar da seed (fallback; requer secret no ambiente)
    if pub is None:
        pub = _derive_pub_from_seed()
    if pub is None:
        print(
            "[verify] missing public key: provide pubkey.json, ORACLE_ED25519_PUB, or ORACLE_ED25519_SEED",
            file=sys.stderr,
        )
        sys.exit(1)

    vk = signing.VerifyKey(pub)
    data = bj.read_bytes()
    sig = Path(bs).read_bytes()
    try:
        vk.verify(data, sig)
    except nacl_exc.BadSignatureError:
        print("Signature verification failed", file=sys.stderr)
        sys.exit(1)

    print(f"[verify] OK for {bj.name}")

if __name__ == "__main__":
    main()
