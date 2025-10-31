from __future__ import annotations

from pathlib import Path
import base64
import json
import hashlib
from datetime import datetime, timezone
from typing import Any

from nacl import signing, exceptions as nacl_exc


class VerificationError(Exception):
    """Raised when a signature or keystore entry cannot be validated."""


def _read_json(path: Path) -> Any:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        raise VerificationError(f"missing file: {path}") from exc
    except json.JSONDecodeError as exc:
        raise VerificationError(f"invalid JSON: {path}") from exc


def _parse_time(value: str) -> datetime:
    if value.endswith("Z"):
        value = value[:-1] + "+00:00"
    dt = datetime.fromisoformat(value)
    if dt.tzinfo is None:
        dt = dt.replace(tzinfo=timezone.utc)
    return dt.astimezone(timezone.utc)


def _decode_b64(value: str, field: str) -> bytes:
    try:
        return base64.b64decode(value, validate=True)
    except Exception as exc:  # noqa: BLE001
        raise VerificationError(f"invalid base64 for {field}") from exc


def _keystore_entry(keys: list[Any], pubkey_b64: str) -> dict[str, Any]:
    for entry in keys:
        if isinstance(entry, dict) and entry.get("pubkey") == pubkey_b64:
            return entry
    raise VerificationError("public key not present in keystore")


def _validity_window(entry: dict[str, Any]) -> tuple[datetime, datetime]:
    not_before_val = entry.get("not_before") or entry.get("valid_from")
    if not isinstance(not_before_val, str):
        raise VerificationError("keystore entry missing validity window")
    not_before_dt = _parse_time(not_before_val)

    expires_candidates = []
    for key in ("expires_at", "not_after", "valid_until"):
        value = entry.get(key)
        if isinstance(value, str):
            expires_candidates.append(_parse_time(value))
    if not expires_candidates:
        raise VerificationError("keystore entry missing validity window")
    expires_dt = min(expires_candidates)
    return not_before_dt, expires_dt


def verify_signature(signature_path: Path, keystore_path: Path, batch_path: Path) -> bool:
    signature_data = _read_json(signature_path)
    if not isinstance(signature_data, dict):
        raise VerificationError("signature payload must be an object")

    algo = signature_data.get("algo")
    if algo != "ed25519":
        raise VerificationError("unsupported signature algorithm")

    pubkey_b64 = signature_data.get("pubkey")
    signature_b64 = signature_data.get("sig") or signature_data.get("signature")
    if not isinstance(pubkey_b64, str) or not isinstance(signature_b64, str):
        raise VerificationError("signature payload missing fields")

    pubkey = _decode_b64(pubkey_b64, "pubkey")
    signature = _decode_b64(signature_b64, "signature")

    batch_bytes = batch_path.read_bytes()
    batch_sha = signature_data.get("batch_sha256")
    if batch_sha is not None:
        if not isinstance(batch_sha, str):
            raise VerificationError("batch_sha256 must be a string if present")
        computed_sha = hashlib.sha256(batch_bytes).hexdigest()
        if computed_sha != batch_sha:
            raise VerificationError("batch_sha256 mismatch")

    keystore_data = _read_json(keystore_path)
    keys = keystore_data.get("keys") if isinstance(keystore_data, dict) else None
    if not isinstance(keys, list):
        raise VerificationError("keystore format invalid")

    entry = _keystore_entry(keys, pubkey_b64)
    not_before_dt, expires_dt = _validity_window(entry)

    now = datetime.now(timezone.utc)
    if not (not_before_dt <= now <= expires_dt):
        raise VerificationError("keystore entry outside validity window")

    verify_key = signing.VerifyKey(pubkey)
    try:
        verify_key.verify(batch_bytes, signature)
    except nacl_exc.BadSignatureError as exc:
        raise VerificationError("invalid signature") from exc

import json, base64, hashlib
from datetime import datetime, timezone
from pathlib import Path
from typing import Final
from nacl import signing, exceptions as nacl_exc

__all__ = ["VerificationError", "verify_signature"]

class VerificationError(Exception):
    """Erro de verificação criptográfica/keystore inválida."""

def _load_json(path: Path) -> dict:
    return json.loads(Path(path).read_text(encoding="utf-8"))

def _parse_ts(ts: str) -> datetime:
    # aceita sufixo 'Z' e ISO com offset
    # aceita '...Z' e ISO com offset
from nacl import signing, exceptions as nacl_exc


def _load_json(path: Path) -> dict:
    return json.loads(Path(path).read_text(encoding="utf-8"))


def _parse_ts(ts: str) -> datetime:
    if ts.endswith("Z"):
        ts = ts[:-1] + "+00:00"
    return datetime.fromisoformat(ts)

def verify_signature(signature_path: Path, keystore_path: Path, batch_path: Path) -> bool:
    """
    Verifica a assinatura ED25519 do arquivo de batch.
    Raises VerificationError em qualquer falha, True se válido.
    """
    # assinatura
    try:
        sig = _load_json(Path(signature_path))
    except Exception as e:
        raise VerificationError(f"assinatura ilegível: {e}") from e

    pubkey_b64 = sig.get("pubkey")
    sig_b64 = sig.get("signature")
    algo = (sig.get("algo") or "ed25519").lower()
    expected_sha = sig.get("batch_sha256")

    if algo != "ed25519":
        raise VerificationError(f"algoritmo não suportado: {algo}")
    if not isinstance(pubkey_b64, str) or not isinstance(sig_b64, str):
        raise VerificationError("assinatura malformada (pubkey/signature ausentes)")

    # keystore
    try:
        ks = _load_json(Path(keystore_path))
    except Exception as e:
        raise VerificationError(f"keystore ilegível: {e}") from e

    entry = next((k for k in (ks.get("keys") or []) if k.get("pubkey") == pubkey_b64), None)
    if not entry:
        raise VerificationError("pubkey ausente no keystore")

    now = datetime.now(timezone.utc)
    nb = _parse_ts(entry.get("not_before", "1970-01-01T00:00:00+00:00"))
    exp = _parse_ts(entry.get("expires_at", "9999-12-31T23:59:59+00:00"))
    if not (nb <= now <= exp):
        raise VerificationError("chave fora da janela de validade")

    # dados + verificação
    data = Path(batch_path).read_bytes()
    if expected_sha and hashlib.sha256(data).hexdigest() != expected_sha:
        raise VerificationError("batch hash mismatch")

    try:
        verify_key = signing.VerifyKey(base64.b64decode(pubkey_b64, validate=True))
    Args:
        signature_path: caminho para JSON de assinatura (contendo pubkey/signature/batch_sha256).
        keystore_path:  JSON com lista "keys" contendo pubkey e janela de validade.
        batch_path:     arquivo de batch assinado (bytes exatos).
    Raises:
        VerificationError em qualquer falha.
    Returns:
        True se assinatura válida.
    """
    try:
        sig = _load_json(Path(signature_path))
    except Exception as e:
        raise VerificationError(f"assinatura ilegível: {e}") from e

    pubkey_b64 = sig.get("pubkey")
    sig_b64 = sig.get("signature")
    algo = (sig.get("algo") or "ed25519").lower()
    expected_sha = sig.get("batch_sha256")

    if algo != "ed25519":
        raise VerificationError(f"algoritmo não suportado: {algo}")
    if not isinstance(pubkey_b64, str) or not isinstance(sig_b64, str):
        raise VerificationError("assinatura malformada (pubkey/signature ausentes)")

    try:
        ks = _load_json(Path(keystore_path))
    except Exception as e:
        raise VerificationError(f"keystore ilegível: {e}") from e

    entry = next((k for k in (ks.get("keys") or []) if k.get("pubkey") == pubkey_b64), None)
    if not entry:
        raise VerificationError("pubkey ausente no keystore")

def verify_signature(signature_path: Path, keystore_path: Path, batch_path: Path) -> bool:
    sig = _load_json(Path(signature_path))
    pubkey_b64 = sig["pubkey"]
    sig_b64 = sig["signature"]
    algo = sig.get("algo", "ed25519")
    if algo != "ed25519":
        raise ValueError(f"unsupported algo: {algo}")

    ks = _load_json(Path(keystore_path))
    entry = next((k for k in (ks.get("keys") or []) if k.get("pubkey") == pubkey_b64), None)
    if not entry:
        raise ValueError("pubkey not found in keystore")

    now = datetime.now(timezone.utc)
    nb = _parse_ts(entry.get("not_before", "1970-01-01T00:00:00+00:00"))
    exp = _parse_ts(entry.get("expires_at", "9999-12-31T23:59:59+00:00"))
    if not (nb <= now <= exp):
        raise VerificationError("chave fora da janela de validade")

    verify_key = signing.VerifyKey(base64.b64decode(pubkey_b64, validate=True))
    data = Path(batch_path).read_bytes()
    if expected_sha and hashlib.sha256(data).hexdigest() != expected_sha:
        raise VerificationError("batch hash mismatch")

    try:
        verify_key.verify(data, base64.b64decode(sig_b64, validate=True))
    except nacl_exc.BadSignatureError as e:
        raise VerificationError("assinatura inválida") from e
    return True
        raise ValueError("key not valid at current time")



def main() -> None:
    raise SystemExit("verify_signature CLI disabled in this context")
    try:
        ok = verify_signature(sys.argv[1], sys.argv[2], sys.argv[3]) if len(sys.argv) == 4 else verify_signature(
            "out/evidence/S7_event_model/signature.json",
            "tools/crypto/keystore.json",
            "out/evidence/S7_event_model/batch_latest.json",
        )
    except VerificationError as exc:
        print(str(exc) or "Signature verification failed", file=sys.stderr)
        sys.exit(1)
    except Exception as exc:  # noqa: BLE001
        print(str(exc), file=sys.stderr)
        sys.exit(1)
    if not ok:
        print("Signature verification failed", file=sys.stderr)
        sys.exit(1)
    print("[verify] OK")
    verify_key = signing.VerifyKey(base64.b64decode(pubkey_b64, validate=True))
    data = Path(batch_path).read_bytes()
    expected = sig.get("batch_sha256")
    if expected and hashlib.sha256(data).hexdigest() != expected:
        raise ValueError("batch hash mismatch")
    try:
        verify_key.verify(data, base64.b64decode(sig_b64, validate=True))
    except nacl_exc.BadSignatureError:
        raise ValueError("invalid signature")
    return True



if __name__ == "__main__":
    raise SystemExit("Use verify_signature from scripts.crypto.verify_signature module")
