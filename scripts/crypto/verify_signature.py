#!/usr/bin/env python3
from __future__ import annotations
import base64
import json
import os
import sys
from pathlib import Path
from typing import Optional, Union
from nacl import signing, exceptions as nacl_exc

PathLike = Union[str, Path]
KEY_ID = os.environ.get("ORACLE_SIGNING_KEY_ID", "s7-active-20251001")

def _default_batch_dir() -> Path:
    return Path("out/evidence/S7_event_model")

def _choose_batch_json_and_sig(bj: Optional[PathLike] = None, bs: Optional[PathLike] = None) -> tuple[Path, Path]:
    root = _default_batch_dir()
    bj_path = Path(bj) if bj is not None else (root / "batch.json")
    if not bj_path.exists():
        candidates = sorted(root.glob("*.json"))
        if not candidates:
            raise FileNotFoundError("no batch JSON found to verify")
        bj_path = candidates[-1]
    bs_path = Path(bs) if bs is not None else (root / "batch.sig")
    if not bs_path.exists():
        cand = bj_path.with_suffix(".sig")
        if cand.exists():
            bs_path = cand
        else:
            raise FileNotFoundError("no signature file found for batch")
    return bj_path, bs_path

def _load_pub_from_pubmeta(dir_: Path) -> Optional[bytes]:
    p = dir_ / "pubkey.json"
    if not p.exists():
        return None
    meta = json.loads(p.read_text(encoding="utf-8"))
    b64 = meta.get("public_key_b64")
    if not isinstance(b64, str):
        return None
    return base64.b64decode(b64, validate=True)

def _pub_from_env() -> Optional[bytes]:
    val = os.environ.get("ORACLE_ED25519_PUB")
    if not val:
        return None
    return base64.b64decode(val, validate=True)

def _pub_from_seed() -> Optional[bytes]:
    seed_b64 = os.environ.get("ORACLE_ED25519_SEED")
    if not seed_b64:
        return None
    raw = base64.b64decode(seed_b64, validate=True)
    if len(raw) != 32:
        raise ValueError("ORACLE_ED25519_SEED is not 32 bytes after base64")
    return bytes(signing.SigningKey(raw).verify_key)

def verify_signature(
    batch_json: Optional[PathLike] = None,
    sig_path: Optional[PathLike] = None,
    pubkey_b64: Optional[str] = None,
) -> bool:
    bj, bs = _choose_batch_json_and_sig(batch_json, sig_path)

    pub: Optional[bytes] = None
    if pubkey_b64:
        pub = base64.b64decode(pubkey_b64, validate=True)
    if pub is None:
        pub = _load_pub_from_pubmeta(bj.parent)
    if pub is None:
        pub = _pub_from_env()
    if pub is None:
        pub = _pub_from_seed()
    if pub is None:
        raise RuntimeError("missing public key: provide pubkey.json, ORACLE_ED25519_PUB, or ORACLE_ED25519_SEED")

    vk = signing.VerifyKey(pub)
    data = Path(bj).read_bytes()
    sig = Path(bs).read_bytes()
    try:
        vk.verify(data, sig)
    except nacl_exc.BadSignatureError:
        return False
    return True

def main() -> None:
    ok = False
    try:
        ok = verify_signature()
    except Exception as e:  # noqa: BLE001
        print(str(e), file=sys.stderr)
        sys.exit(1)
    if not ok:
        print("Signature verification failed", file=sys.stderr)
        sys.exit(1)
    print("[verify] OK")

if __name__ == "__main__":
    main()
