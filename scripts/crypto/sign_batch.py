from __future__ import annotations
import os, sys, json, base64, hashlib, datetime
from pathlib import Path
from typing import Union

try:
    from nacl import signing, exceptions as n_ex
except Exception:  # pragma: no cover
    try:
        from nacl import signing, exceptions as n_ex  # type: ignore
    except Exception as e:
        sys.stderr.write(f"[sign] NaCl indisponível (vendored/pip): {e}\n")
        raise

PathLike = Union[str, Path]
SIGNATURE_PATH: Path = Path("out/evidence/S7_event_model/batch.signature.json")
ENV_PRIMARY  = "ORACLE_ED25519_SEED"
ENV_FALLBACK = "CE_SIGN_SEED_B64"

def _ensure_dir(p: Path) -> None:
    p.mkdir(parents=True, exist_ok=True)

def _b64(b: bytes) -> str:
    return base64.b64encode(b).decode("ascii")

def _parse_time(ts):
    if not isinstance(ts, str):
        return None
    t = ts[:-1] + "+00:00" if ts.endswith("Z") else ts
    try:
        from datetime import datetime
        return datetime.fromisoformat(t)
    except Exception:
        return None

def _enforce_keystore_policy(keystore_path: Path | None, pubkey_b64: str) -> None:
    if not keystore_path:
        return
    kp = Path(keystore_path)
    if not kp.exists():
        return
    raw = kp.read_text()
    try:
        ks = json.loads(raw)
    except Exception as e:
        raise SystemExit(f"[sign] invalid keystore json: {e}")

    from datetime import datetime, timezone
    now = datetime.now(timezone.utc)

    # Esquema A (top-level)
    top_pub = ks.get("pubkey_b64") or ks.get("pubkey")
    if isinstance(top_pub, str) and top_pub:
        if top_pub != pubkey_b64:
            raise SystemExit("[sign] pubkey mismatch against keystore (top-level)")
        nb = _parse_time(ks.get("not_before"))
        exp = _parse_time(ks.get("expires_at") or ks.get("expire_at") or ks.get("not_after"))
        if nb and now < nb:
            raise SystemExit("[sign] key not valid yet (not_before)")
        if exp and now >= exp:
            raise SystemExit("[sign] key expired (expires_at/not_after)")
        allowed = ks.get("allowed_pubkeys")
        if isinstance(allowed, list) and allowed and pubkey_b64 not in allowed:
            raise SystemExit("[sign] pubkey not whitelisted in keystore")
        status = ks.get("status")
        if isinstance(status, str) and status.lower() not in ("active","valid","enabled",""):
            raise SystemExit("[sign] key status not active")
        return

    # Esquema B (keys[])
    keys = ks.get("keys")
    if isinstance(keys, list):
        def _kpub(k): return (k.get("pubkey_b64") or k.get("pubkey")) if isinstance(k, dict) else None
        matches = [k for k in keys if _kpub(k) == pubkey_b64]
        if not matches:
            raise SystemExit("[sign] pubkey not found in keystore keys[]")
        k = matches[0]
        nb = _parse_time(k.get("not_before"))
        exp = _parse_time(k.get("expires_at") or k.get("expire_at") or k.get("not_after"))
        if nb and now < nb:
            raise SystemExit("[sign] key not valid yet (not_before)")
        if exp and now >= exp:
            raise SystemExit("[sign] key expired (expires_at/not_after)")
        status = k.get("status")
        if isinstance(status, str) and status.lower() not in ("active","valid","enabled",""):
            raise SystemExit("[sign] key status not active")
        return

    # formato desconhecido -> leniente
    return

def sign_batch(batch_path: PathLike, keystore_path: PathLike | None = None) -> Path:
    seed_b64 = os.environ.get(ENV_PRIMARY) or os.environ.get(ENV_FALLBACK)
    if not seed_b64:
        raise SystemExit("[sign] missing env ORACLE_ED25519_SEED/CE_SIGN_SEED_B64")
    try:
        seed = base64.b64decode(seed_b64, validate=True)
    except Exception as e:
        raise SystemExit(f"[sign] bad base64 seed: {e}")
    if len(seed) != 32:
        raise SystemExit("[sign] seed must be 32 bytes (ed25519)")

    sk = signing.SigningKey(seed)
    vk = sk.verify_key
    pubkey_b64 = _b64(bytes(vk))

    if keystore_path:
        _enforce_keystore_policy(Path(keystore_path), pubkey_b64)

    bp = Path(batch_path)
    msg = bp.read_bytes()

    sig = sk.sign(msg).signature  # assinatura só (64 bytes)
    doc = {
        "alg": "ed25519",
        "created_at": datetime.datetime.utcnow().isoformat(timespec="seconds") + "Z",
        "path": str(bp),
        "sha256": hashlib.sha256(msg).hexdigest(),
        "pubkey_b64": pubkey_b64,
        "sig": _b64(sig)
    }
    _ensure_dir(SIGNATURE_PATH.parent)
    SIGNATURE_PATH.write_text(json.dumps(doc, ensure_ascii=False, indent=2))
    return SIGNATURE_PATH
