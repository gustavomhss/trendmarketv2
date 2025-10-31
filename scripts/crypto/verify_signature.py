#!/usr/bin/env python3
from __future__ import annotations

import base64
import binascii
import hashlib
import json
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Dict, Union

from scripts.crypto._ed25519 import BadSignatureError, VerifyKey

PathLike = Union[str, Path]


class VerificationError(Exception):
    """Erro de verificação de assinatura (chave ausente ou assinatura inválida)."""


def _as_path(value: PathLike) -> Path:
    path = Path(value)
    if not path.exists():
        raise VerificationError(f"artefacto ausente: {path}")
    return path


def _load_json(path: Path) -> Dict[str, object]:
    try:
        with path.open("r", encoding="utf-8") as handle:
            data = json.load(handle)
    except json.JSONDecodeError as exc:
        raise VerificationError(f"JSON inválido em {path}: {exc}") from exc
    if not isinstance(data, dict):
        raise VerificationError(f"{path} deve conter um objeto JSON")
    return data


def _decode_b64(value: object, field: str) -> bytes:
    if not isinstance(value, str):
        raise VerificationError(f"campo {field} deve ser base64 str")
    try:
        return base64.b64decode(value, validate=True)
    except (ValueError, binascii.Error) as exc:  # type: ignore[name-defined]
        raise VerificationError(f"campo {field} não é base64 válido") from exc


def _find_key(keystore: Dict[str, object], kid: str) -> Dict[str, object]:
    keys = keystore.get("keys")
    if not isinstance(keys, list):
        raise VerificationError("keystore sem lista de chaves")
    for entry in keys:
        if isinstance(entry, dict) and entry.get("kid") == kid:
            return entry
    raise VerificationError(f"chave {kid} não encontrada no keystore")


def _parse_timestamp(value: object, field: str) -> datetime:
    if not isinstance(value, str):
        raise VerificationError(f"campo {field} deve ser string ISO8601")
    try:
        return datetime.fromisoformat(value.replace("Z", "+00:00")).astimezone(timezone.utc)
    except ValueError as exc:
        raise VerificationError(f"timestamp inválido em {field}") from exc


def _batch_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(8192), b""):
            digest.update(chunk)
    return digest.hexdigest()


def verify_signature(signature_path: PathLike, keystore_path: PathLike, batch_path: PathLike) -> bool:
    sig_file = _as_path(signature_path)
    keystore_file = _as_path(keystore_path)
    batch_file = _as_path(batch_path)

    signature = _load_json(sig_file)
    keystore = _load_json(keystore_file)
    batch = _load_json(batch_file)

    alg = signature.get("alg")
    if not isinstance(alg, str) or alg.lower() != "ed25519":
        raise VerificationError("algoritmo inválido na assinatura")

    kid = signature.get("kid")
    if not isinstance(kid, str) or not kid:
        raise VerificationError("assinatura sem kid")

    sig_bytes = _decode_b64(signature.get("sig"), "sig")
    if len(sig_bytes) != 64:
        raise VerificationError("assinatura deve ter 64 bytes")

    pubkey_b64 = signature.get("pubkey")
    pubkey_bytes = _decode_b64(pubkey_b64, "pubkey")
    if len(pubkey_bytes) != 32:
        raise VerificationError("chave pública deve ter 32 bytes")

    merkle_root = signature.get("merkle_root")
    batch_ts = signature.get("batch_ts")
    if not isinstance(merkle_root, str) or not merkle_root:
        raise VerificationError("assinatura sem merkle_root")
    if not isinstance(batch_ts, str) or not batch_ts:
        raise VerificationError("assinatura sem batch_ts")

    batch_merkle = batch.get("merkle_root")
    batch_time = batch.get("batch_ts")
    if batch_merkle != merkle_root or batch_time != batch_ts:
        raise VerificationError("batch e assinatura divergentes")

    expected_hash = signature.get("batch_sha256")
    if isinstance(expected_hash, str):
        if expected_hash != _batch_sha256(batch_file):
            raise VerificationError("hash do batch divergente")

    key_entry = _find_key(keystore, kid)
    key_alg = key_entry.get("alg")
    if not isinstance(key_alg, str) or key_alg.lower() != "ed25519":
        raise VerificationError("algoritmo inválido no keystore")

    key_pub = key_entry.get("pubkey")
    if key_pub != pubkey_b64:
        raise VerificationError("pubkey da assinatura não bate com keystore")

    created = _parse_timestamp(key_entry.get("created_at"), "created_at")
    not_after = _parse_timestamp(key_entry.get("not_after"), "not_after")
    reference_time = _parse_timestamp(batch_ts, "batch_ts")
    if not (created <= reference_time <= not_after):
        raise VerificationError("assinatura fora da janela de validade da chave")

    status = key_entry.get("status")
    if status not in {"active", "retiring"}:
        raise VerificationError("chave não está ativa")

    message = f"{merkle_root}|{batch_ts}".encode("utf-8")
    verify_key = VerifyKey(pubkey_bytes)
    try:
        verify_key.verify(message, sig_bytes)
    except BadSignatureError as exc:
        raise VerificationError("assinatura inválida") from exc

    return True


def main() -> None:
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


if __name__ == "__main__":
    main()
