from __future__ import annotations
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
