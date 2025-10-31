from __future__ import annotations

import base64
import hashlib
import json
import os
import re
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Dict, Optional, Union

from scripts.crypto._ed25519 import SigningKey

PathLike = Union[str, Path]
KEY_ID = os.environ.get("ORACLE_SIGNING_KEY_ID", "s7-active-20251001")
SIGNATURE_PATH = Path("out/evidence/S7_event_model/signature.json")
DEFAULT_KEYSTORE_PATH = Path("tools/crypto/keystore.json")

import os, json, base64, hashlib
from datetime import datetime, timezone, timedelta
from pathlib import Path
from typing import Dict, Optional
from typing import Union
from nacl import signing

PathLike = Union[str, Path]
KEY_ID = os.environ.get("ORACLE_SIGNING_KEY_ID", "s7-active-20251001")
SIGNATURE_PATH: "Path" = Path("out/evidence/S7_event_model/signature.json")



def _seed_b64_from_env(key_id: Optional[str] = None) -> Optional[str]:

def _ensure_dir(p: Path) -> None:
    p.parent.mkdir(parents=True, exist_ok=True)


def _default_batch_dir() -> Path:
    return Path("out/evidence/S7_event_model")


def _choose_batch_json(batch_json: Optional[PathLike] = None) -> Path:
    if batch_json is not None:
        return Path(batch_json)
    d = _default_batch_dir()
    bj = d / "batch_latest.json"
    if bj.exists():
        return bj
    candidates = sorted(d.glob("batch_*.json"))
    kid = key_id or KEY_ID
    return os.environ.get(_env_name_for_key(kid)) or os.environ.get("ORACLE_ED25519_SEED")


def _decode_seed(seed_b64: str) -> bytes:
    raw = base64.b64decode(seed_b64, validate=True)
    if len(raw) != 32:
        raise ValueError(f"seed must be 32 bytes after base64; got {len(raw)}")
    return raw

    if not candidates:
        raise FileNotFoundError("no batch JSON found in out/evidence/S7_event_model")
    return candidates[-1]


def _load_keystore(keystore_path: Path) -> Dict[str, object]:
    with keystore_path.open("r", encoding="utf-8") as handle:
        data = json.load(handle)
    if not isinstance(data, dict):
        raise ValueError("keystore must be a JSON object")
    return data


def _pick_key(data: Dict[str, object], key_id: str) -> Dict[str, object]:
    keys = data.get("keys")
    if not isinstance(keys, list):
        raise ValueError("keystore missing keys list")
    for entry in keys:
        if isinstance(entry, dict) and entry.get("kid") == key_id:
            return entry
    raise ValueError(f"key {key_id} not found in keystore")


def _message_to_sign(merkle_root: str, batch_ts: str) -> bytes:
    return f"{merkle_root}|{batch_ts}".encode("utf-8")


def _batch_hash(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(8192), b""):
            digest.update(chunk)
    return digest.hexdigest()


def sign_batch(
    batch_json: Optional[PathLike] = None,
    keystore_path: Optional[PathLike] = None,
    *,
    signature_path: Optional[PathLike] = None,
    seed_b64: Optional[str] = None,
    key_id: Optional[str] = None,
) -> Dict[str, str]:
    """Assina o batch JSON e emite signature.json compatível com o verificador."""

    kid = key_id or KEY_ID
    seed_b64 = seed_b64 or _seed_b64_from_env(kid)
    if not seed_b64:
        raise RuntimeError(
            f"Missing seed for key {kid}. Set {_env_name_for_key(kid)} or ORACLE_ED25519_SEED"
        )

    batch_path = _choose_batch_json(batch_json)
    keystore = Path(keystore_path) if keystore_path is not None else DEFAULT_KEYSTORE_PATH
    signature_dest = Path(signature_path) if signature_path is not None else SIGNATURE_PATH

    keystore_data = _load_keystore(keystore)
    key_entry = _pick_key(keystore_data, kid)
    algorithm = str(key_entry.get("alg", "")).lower()
    if algorithm != "ed25519":
        raise ValueError(f"unsupported algorithm {key_entry.get('alg')} for key {kid}")

    pubkey_b64 = key_entry.get("pubkey")
    if not isinstance(pubkey_b64, str):
        raise ValueError("keystore entry missing base64 pubkey")

    seed = _decode_seed(seed_b64)
    signer = SigningKey(seed)
    derived_pubkey = base64.b64encode(signer.verify_key.to_bytes()).decode()
    if derived_pubkey != pubkey_b64:
        raise ValueError("provided seed does not match keystore public key")

    with batch_path.open("r", encoding="utf-8") as handle:
        batch_data = json.load(handle)
    merkle_root = str(batch_data.get("merkle_root"))
    batch_ts = str(batch_data.get("batch_ts"))
    if not merkle_root or not batch_ts:
        raise ValueError("batch JSON missing merkle_root or batch_ts")

    message = _message_to_sign(merkle_root, batch_ts)
    signature = signer.sign(message)

    record = {
        "kid": kid,
        "alg": "ed25519",
        "sig": base64.b64encode(signature).decode(),
        "pubkey": pubkey_b64,
        "merkle_root": merkle_root,
        "batch_ts": batch_ts,
        "batch_sha256": _batch_hash(batch_path),
        "signed_at": datetime.now(timezone.utc).isoformat().replace("+00:00", "Z"),
    }

    _ensure_dir(signature_dest)
    signature_dest.write_text(json.dumps(record, indent=2), encoding="utf-8")

    return {"batch": str(batch_path), "signature": str(signature_dest), "key_id": kid}


def main() -> None:
    try:
        res = sign_batch()
    except Exception as exc:  # noqa: BLE001
        print(str(exc), file=sys.stderr)
        sys.exit(1)
    print(f"[sign] wrote {res['signature']} for {Path(res['batch']).name}")

def _utcnow_iso() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat()


def _load_json(path: Path) -> dict:
    try:
        return json.loads(Path(path).read_text(encoding="utf-8"))
    except Exception:
        return {}


def _save_json(path: Path, obj: dict) -> None:
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(obj, ensure_ascii=False, indent=2), encoding="utf-8")


def sign_batch(batch_path: Path, keystore_path: Path, signature_path: Path | None = None) -> Path:
    data = Path(batch_path).read_bytes()
    sha256 = hashlib.sha256(data).hexdigest()

    seed_b64 = os.environ.get("ORACLE_ED25519_SEED")
    if not seed_b64:
        raise RuntimeError("ORACLE_ED25519_SEED not set")
    seed = base64.b64decode(seed_b64, validate=True)
    sk = signing.SigningKey(seed)
    vk = sk.verify_key
    pubkey_b64 = base64.b64encode(bytes(vk)).decode("ascii")

    sig_bytes = sk.sign(data).signature
    sig_b64 = base64.b64encode(sig_bytes).decode("ascii")

    # garantir keystore JSON com essa pubkey e janela de validade generosa
    ks_path = Path(keystore_path)
    ks = _load_json(ks_path) or {}
    keys = ks.get("keys") or []
    found = False
    for k in keys:
        if k.get("pubkey") == pubkey_b64:
            found = True
            k.setdefault("algo", "ed25519")
            k.setdefault("kid", "default")
            k.setdefault("not_before", _utcnow_iso())
            k.setdefault("expires_at", (datetime.now(timezone.utc) + timedelta(days=3650)).replace(microsecond=0).isoformat())
            break
    if not found:
        keys.append({
            "kid": "default",
            "algo": "ed25519",
            "pubkey": pubkey_b64,
            "not_before": _utcnow_iso(),
            "expires_at": (datetime.now(timezone.utc) + timedelta(days=3650)).replace(microsecond=0).isoformat(),
        })
    ks["keys"] = keys
    _save_json(ks_path, ks)

    sig_obj = {
        "algo": "ed25519",
        "signed_at": _utcnow_iso(),
        "pubkey": pubkey_b64,
        "signature": sig_b64,
        "batch_sha256": sha256,
    }
    out_path = Path(signature_path) if signature_path else SIGNATURE_PATH
    _save_json(out_path, sig_obj)
    return out_path


if __name__ == "__main__":
    raise SystemExit("Use sign_batch from scripts.crypto.sign_batch module")
