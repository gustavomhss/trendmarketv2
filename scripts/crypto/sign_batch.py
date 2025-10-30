from __future__ import annotations
import os, json, base64, hashlib
from datetime import datetime, timezone, timedelta
from pathlib import Path
from nacl import signing

PathLike = Union[str, Path]
KEY_ID = os.environ.get("ORACLE_SIGNING_KEY_ID", "s7-active-20251001")
SIGNATURE_PATH: "Path" = Path("out/evidence/S7_event_model/signature.json")


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
