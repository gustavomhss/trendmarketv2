from __future__ import annotations

import argparse
import base64
import hashlib
import importlib.util
import json
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable, Mapping

_REPO_ROOT = Path(__file__).resolve().parents[2]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

for _name in [key for key in list(sys.modules) if key == "nacl" or key.startswith("nacl.")]:
    sys.modules.pop(_name, None)

_signing_spec = importlib.util.spec_from_file_location(
    "nacl.signing", _REPO_ROOT / "nacl" / "signing.py"
)
if _signing_spec is None or _signing_spec.loader is None:
    raise RuntimeError("cannot load local nacl.signing stub")
signing = importlib.util.module_from_spec(_signing_spec)
sys.modules["nacl.signing"] = signing
_signing_spec.loader.exec_module(signing)

_exceptions_spec = importlib.util.spec_from_file_location(
    "nacl.exceptions", _REPO_ROOT / "nacl" / "exceptions.py"
)
if _exceptions_spec is None or _exceptions_spec.loader is None:
    raise RuntimeError("cannot load local nacl.exceptions stub")
nacl_exceptions = importlib.util.module_from_spec(_exceptions_spec)
sys.modules["nacl.exceptions"] = nacl_exceptions
_exceptions_spec.loader.exec_module(nacl_exceptions)

from .sign_batch import (
    BATCH_PATH,
    DEFAULT_DOMAIN_TAG,
    PUBKEY_PATH,
    _canonical_bytes,
    _canonical_payload,
    _extract_pem_bytes,
)


@dataclass(slots=True)
class VerificationError(RuntimeError):
    message: str
    exit_code: int = 51

    def __str__(self) -> str:  # pragma: no cover
        return self.message


def _read_json(path: Path) -> Mapping[str, Any]:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        raise VerificationError(f"file not found: {path}", exit_code=52) from exc
    except json.JSONDecodeError as exc:
        raise VerificationError(f"invalid json: {path}", exit_code=52) from exc


def _load_public_key(path: Path) -> bytes:
    raw = _extract_pem_bytes(path, "-----BEGIN ED25519 PUBLIC KEY-----")
    if len(raw) != 32:
        raise VerificationError("ed25519 public key must be 32 bytes", exit_code=52)
    return raw


def _decode_b64(value: str, label: str) -> bytes:
    try:
        return base64.b64decode(value, validate=True)
    except Exception as exc:  # pragma: no cover - defensive
        raise VerificationError(f"invalid base64 for {label}") from exc


def verify_signature(
    batch_path: Path | None = None,
    *,
    signature_path: Path,
    pubkey_path: Path | None = None,
    domain_tag: str = DEFAULT_DOMAIN_TAG,
) -> dict[str, Any]:
    batch_path = Path(batch_path or BATCH_PATH)
    signature_path = Path(signature_path)
    pubkey_path = Path(pubkey_path or PUBKEY_PATH)

    batch_data = _read_json(batch_path)
    expected_payload = _canonical_payload(batch_data)
    payload_bytes = _canonical_bytes(expected_payload)
    expected_payload_sha = hashlib.sha256(payload_bytes).hexdigest()

    signature_doc = _read_json(signature_path)

    if signature_doc.get("schema_version") != expected_payload["schema_version"]:
        raise VerificationError("schema_version mismatch", exit_code=52)

    domain = domain_tag if domain_tag.endswith("\n") else f"{domain_tag}\n"
    if signature_doc.get("domain_tag") != domain:
        raise VerificationError("domain_tag mismatch", exit_code=52)

    if signature_doc.get("payload") != expected_payload:
        raise VerificationError("payload does not match batch", exit_code=52)

    payload_sha = signature_doc.get("payload_sha256")
    if payload_sha != expected_payload_sha:
        raise VerificationError("payload_sha256 mismatch", exit_code=52)

    batch_bytes = batch_path.read_bytes()
    batch_sha = hashlib.sha256(batch_bytes).hexdigest()
    if signature_doc.get("batch_sha256") != batch_sha:
        raise VerificationError("batch_sha256 mismatch", exit_code=52)

    signature_b64 = signature_doc.get("signature")
    public_b64 = signature_doc.get("public_key")
    if not isinstance(signature_b64, str) or not isinstance(public_b64, str):
        raise VerificationError("signature/public_key missing", exit_code=52)
    signature_bytes = _decode_b64(signature_b64, "signature")
    public_bytes = _decode_b64(public_b64, "public_key")

    expected_public = _load_public_key(pubkey_path)
    if expected_public != public_bytes:
        raise VerificationError("public key does not match fixture", exit_code=52)

    message = domain.encode("utf-8") + payload_bytes
    verify_key = signing.VerifyKey(public_bytes)
    try:
        verify_key.verify(message, signature_bytes)
    except nacl_exceptions.BadSignatureError as exc:
        raise VerificationError("invalid signature") from exc

    return {
        "ok": True,
        "payload_sha256": expected_payload_sha,
        "batch_sha256": batch_sha,
        "signature_sha256": hashlib.sha256(signature_bytes).hexdigest(),
    }


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Verify canonical batch signature")
    parser.add_argument("--in", dest="batch", default=str(BATCH_PATH))
    parser.add_argument("--sig", dest="signature", required=True)
    parser.add_argument("--pubkey", dest="pubkey", default=str(PUBKEY_PATH))
    parser.add_argument("--domain-tag", dest="domain_tag", default=DEFAULT_DOMAIN_TAG)
    return parser


def main(argv: Iterable[str] | None = None) -> int:
    parser = _build_parser()
    args = parser.parse_args(list(argv) if argv is not None else None)
    try:
        result = verify_signature(
            Path(args.batch),
            signature_path=Path(args.signature),
            pubkey_path=Path(args.pubkey),
            domain_tag=args.domain_tag,
        )
    except VerificationError as exc:
        payload = {"ok": False, "error": exc.message}
        print(json.dumps(payload, separators=(",", ":"), sort_keys=True), flush=True)
        return exc.exit_code

    print(json.dumps(result, separators=(",", ":"), sort_keys=True), flush=True)
    return 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
