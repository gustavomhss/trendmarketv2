from __future__ import annotations
import json, base64, hashlib, sys, datetime
from pathlib import Path

try:
    from nacl import signing, exceptions as n_ex
except Exception:  # pragma: no cover
    try:
        from nacl import signing, exceptions as n_ex  # type: ignore
    except Exception as e:
        sys.stderr.write(f"[verify] NaCl indisponível (vendored/pip): {e}\n")
        raise

class VerificationError(Exception):
    """Falha de verificação criptográfica ou de integridade."""

def _parse_time(ts):
    if not isinstance(ts, str):
        return None
    t = ts[:-1] + "+00:00" if ts.endswith("Z") else ts
    try:
        return datetime.datetime.fromisoformat(t)
    except Exception:
        return None

def _coalesce_exp(meta: dict) -> datetime.datetime | None:
    candidates = [_parse_time(meta.get(k)) for k in ("not_after", "expires_at", "expire_at")]
    exps = [x for x in candidates if x is not None]
    return min(exps) if exps else None

def _enforce_keystore_policy(keystore_path: Path | None, pubkey_b64: str) -> None:
    if not keystore_path:
        return
    kp = Path(keystore_path)
    if not kp.exists():
        return
    try:
        ks = json.loads(kp.read_text())
    except Exception as e:
        raise VerificationError(f"invalid keystore json: {e}")

    now = datetime.datetime.now(datetime.UTC)

    top_pub = ks.get("pubkey_b64") or ks.get("pubkey")
    if isinstance(top_pub, str) and top_pub:
        if top_pub != pubkey_b64:
            raise VerificationError("pubkey mismatch against keystore (top-level)")
        nb  = _parse_time(ks.get("not_before"))
        exp = _coalesce_exp(ks)
        if nb and now < nb:
            raise VerificationError("key not valid yet (not_before)")
        if exp and now >= exp:
            raise VerificationError("key expired (not_after/expires_at)")
        allowed = ks.get("allowed_pubkeys")
        if isinstance(allowed, list) and allowed and pubkey_b64 not in allowed:
            raise VerificationError("pubkey not whitelisted in keystore")
        status = ks.get("status")
        if isinstance(status, str) and status.lower() not in ("active","valid","enabled",""):
            raise VerificationError("key status not active")
        return

    keys = ks.get("keys")
    if isinstance(keys, list):
        def _kpub(k): return (k.get("pubkey_b64") or k.get("pubkey")) if isinstance(k, dict) else None
        matches = [k for k in keys if _kpub(k) == pubkey_b64]
        if not matches:
            raise VerificationError("pubkey not found in keystore keys[]")
        k = matches[0]
        nb  = _parse_time(k.get("not_before"))
        exp = _coalesce_exp(k)
        if nb and now < nb:
            raise VerificationError("key not valid yet (not_before)")
        if exp and now >= exp:
            raise VerificationError("key expired (not_after/expires_at)")
        status = k.get("status")
        if isinstance(status, str) and status.lower() not in ("active","valid","enabled",""):
            raise VerificationError("key status not active")
        return
    return

def verify_signature(signature_path: str | Path, keystore_path: str | Path | None, batch_path: str | Path) -> bool:
    sp = Path(signature_path)
    bp = Path(batch_path)
    if not sp.is_file():
        raise VerificationError(f"signature file not found: {sp}")
    if not bp.is_file():
        raise VerificationError(f"batch file not found: {bp}")

    try:
        data = json.loads(sp.read_text())
    except Exception as e:
        raise VerificationError(f"invalid signature json: {e}")

    try:
        sig = base64.b64decode(data["sig"], validate=True)
    except KeyError:
        raise VerificationError("missing 'sig' field")
    except Exception as e:
        raise VerificationError(f"invalid 'sig' (b64): {e}")

    pubkey_b64 = data.get("pubkey_b64") or data.get("pubkey")
    if not isinstance(pubkey_b64, str) or not pubkey_b64:
        raise VerificationError("missing 'pubkey_b64' in signature")

    if keystore_path:
        _enforce_keystore_policy(Path(keystore_path), pubkey_b64)

    try:
        vk = signing.VerifyKey(base64.b64decode(pubkey_b64, validate=True))
    except Exception as e:
        raise VerificationError(f"invalid pubkey_b64: {e}")

    msg = bp.read_bytes()
    try:
        vk.verify(msg, sig)
    except Exception as e:
        raise VerificationError(f"bad signature: {e}")

    if "sha256" in data:
        sha = hashlib.sha256(msg).hexdigest()
        if data["sha256"] != sha:
            raise VerificationError("digest mismatch (sha256)")

    return True
