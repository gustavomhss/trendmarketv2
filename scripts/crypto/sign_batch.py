#!/usr/bin/env python3
from __future__ import annotations
import base64
import json
import os
import re
import sys
from pathlib import Path
from typing import Dict, Optional, Union
from nacl import signing

PathLike = Union[str, Path]
KEY_ID = os.environ.get("ORACLE_SIGNING_KEY_ID", "s7-active-20251001")

def _env_name_for_key(key_id: str) -> str:
    safe = re.sub(r"[^A-Za-z0-9_]", "_", key_id.upper())
    return f"ORACLE_ED25519_SEED_{safe}"

def _seed_b64_from_env(key_id: Optional[str] = None) -> Optional[str]:
    kid = key_id or KEY_ID
    return os.environ.get(_env_name_for_key(kid)) or os.environ.get("ORACLE_ED25519_SEED")

def _decode_seed(seed_b64: str) -> bytes:
    raw = base64.b64decode(seed_b64, validate=True)
    if len(raw) != 32:
        raise ValueError(f"seed must be 32 bytes after base64; got {len(raw)}")
    return raw

def _ensure_dir(p: Path) -> None:
    p.parent.mkdir(parents=True, exist_ok=True)

def _default_batch_dir() -> Path:
    return Path("out/evidence/S7_event_model")

def _choose_batch_json(batch_json: Optional[PathLike] = None) -> Path:
    if batch_json is not None:
        return Path(batch_json)
    d = _default_batch_dir()
    bj = d / "batch.json"
    if bj.exists():
        return bj
    cand = sorted(d.glob("*.json"))
    if not cand:
        raise FileNotFoundError("no batch JSON found in out/evidence/S7_event_model")
    return cand[-1]

def sign_batch(
    batch_json: Optional[PathLike] = None,
    out_sig: Optional[PathLike] = None,
    seed_b64: Optional[str] = None,
    key_id: Optional[str] = None,
) -> Dict[str, str]:
    """
    Assina o batch JSON e emite:
      - assinatura (batch.sig por padrão)
      - pubkey.json (chave pública em base64)
    Retorna dict com caminhos e public_key_b64.
    """
    kid = key_id or KEY_ID
    seed_b64 = seed_b64 or _seed_b64_from_env(kid)
    if not seed_b64:
        raise RuntimeError(f"Missing seed for key {kid}. Set {_env_name_for_key(kid)} or ORACLE_ED25519_SEED")

    seed = _decode_seed(seed_b64)
    signer = signing.SigningKey(seed)
    verify_key = signer.verify_key
    pub_b64 = base64.b64encode(bytes(verify_key)).decode()

    bj = _choose_batch_json(batch_json)
    sig_path = Path(out_sig) if out_sig is not None else (bj.parent / "batch.sig")
    _ensure_dir(sig_path)

    data = bj.read_bytes()
    signature = signer.sign(data).signature  # 64 bytes
    sig_path.write_bytes(signature)

    pubmeta = {"alg": "Ed25519", "key_id": kid, "public_key_b64": pub_b64}
    (bj.parent / "pubkey.json").write_text(json.dumps(pubmeta, indent=2), encoding="utf-8")

    return {"batch": str(bj), "sig": str(sig_path), "public_key_b64": pub_b64, "key_id": kid}

def main() -> None:
    try:
        res = sign_batch()
    except Exception as e:  # noqa: BLE001
        print(str(e), file=sys.stderr)
        sys.exit(1)
    print(f"[sign] wrote {res['sig']} and pubkey.json for {Path(res['batch']).name}")

if __name__ == "__main__":
    main()
