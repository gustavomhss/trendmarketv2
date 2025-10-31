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
import base64
import hashlib
import json
import os
from datetime import datetime, timezone
from hashlib import sha256
from pathlib import Path
from typing import Any, Dict, Optional

try:  # pragma: no cover - fallback when PyNaCl is unavailable
    from nacl import signing  # type: ignore
except ModuleNotFoundError:  # pragma: no cover - exercised in CI image without PyNaCl
    from tools.crypto import ed25519 as _ed25519

    class _SignedMessage:
        def __init__(self, signature: bytes) -> None:
            self.signature = signature

    class _VerifyKey:
        def __init__(self, key: bytes) -> None:
            if len(key) != 32:
                raise ValueError("Ed25519 public key must be 32 bytes")
            self._key = key

        def verify(self, message: bytes, signature: bytes) -> bytes:
            if not _ed25519.verify(signature, message, self._key):
                raise ValueError("invalid signature")
            return message

        def __bytes__(self) -> bytes:
            return self._key

    class _SigningKey:
        def __init__(self, seed: bytes) -> None:
            if len(seed) != 32:
                raise ValueError("Ed25519 seed must be 32 bytes")
            self._seed = seed
            self.verify_key = _VerifyKey(_ed25519.public_key(seed))

        def sign(self, message: bytes) -> _SignedMessage:
            signature = _ed25519.sign(message, self._seed, bytes(self.verify_key))
            return _SignedMessage(signature)

    class _SigningModule:
        SigningKey = _SigningKey
        VerifyKey = _VerifyKey

    signing = _SigningModule()  # type: ignore

SIGNATURE_PATH = Path("out/evidence/S7_event_model/signature.json")


def _ensure_dir(path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)


def _load_json(path: Path) -> Dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _decode_seed(seed_b64: str) -> bytes:
    raw = base64.b64decode(seed_b64, validate=True)
    if len(raw) != 32:
        raise ValueError("Ed25519 seed must be 32 bytes after base64 decoding")
    return raw


def _active_key_entry(keystore: Dict[str, Any]) -> Dict[str, Any]:
    keys = keystore.get("keys")
    if not isinstance(keys, list):
        raise ValueError("keystore missing 'keys' list")

    for entry in keys:
        if isinstance(entry, dict) and entry.get("status") == "active":
            return entry

    for entry in keys:
        if isinstance(entry, dict):
            return entry

    raise ValueError("keystore does not contain usable keys")


def _seed_from_keystore(entry: Dict[str, Any]) -> Optional[str]:
    for field in ("seed", "seed_b64", "secret_key", "private_key", "sk"):
        value = entry.get(field)
        if isinstance(value, str):
            return value
    return None


def _now_iso_z() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def sign_batch(batch_path: Path, keystore_path: Path, signature_path: Optional[Path] = None) -> Path:
    keystore_data = _load_json(keystore_path)
    key_entry = _active_key_entry(keystore_data)
    key_id = key_entry.get("kid")
    if not isinstance(key_id, str) or not key_id:
        raise ValueError("active key is missing 'kid'")

    seed_b64 = os.environ.get("ORACLE_ED25519_SEED")
    if not seed_b64:
        seed_b64 = _seed_from_keystore(key_entry)
    if not seed_b64:
        raise RuntimeError("missing Ed25519 seed: provide ORACLE_ED25519_SEED or keystore seed entry")

    seed = _decode_seed(seed_b64)
    signing_key = signing.SigningKey(seed)
    public_key = signing_key.verify_key
    public_key_b64 = base64.b64encode(bytes(public_key)).decode("utf-8")

    keystore_pub = key_entry.get("pubkey") or key_entry.get("public_key")
    if isinstance(keystore_pub, str):
        expected_pub = base64.b64decode(keystore_pub, validate=True)
        if expected_pub != bytes(public_key):
            raise RuntimeError("provided seed does not match keystore public key")

    target_path = signature_path or SIGNATURE_PATH
    _ensure_dir(target_path)

    batch_bytes = batch_path.read_bytes()
    signature = signing_key.sign(batch_bytes).signature
    signature_b64 = base64.b64encode(signature).decode("utf-8")
    batch_hash = sha256(batch_bytes).hexdigest()

    payload = {
        "algorithm": "ed25519",
        "key_id": key_id,
        "public_key_b64": public_key_b64,
        "batch_sha256": batch_hash,
        "signature_b64": signature_b64,
        "sig": signature_b64,
        "signed_at": _now_iso_z(),
    }

    target_path.write_text(json.dumps(payload, ensure_ascii=False, sort_keys=True), encoding="utf-8")
    return target_path
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
