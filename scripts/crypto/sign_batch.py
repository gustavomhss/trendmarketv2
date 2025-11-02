from __future__ import annotations

import argparse
import base64
import datetime as dt
import hashlib
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable, Mapping

from nacl import exceptions as nacl_exceptions
from nacl import signing

SIGNATURE_PATH = "out/signatures/latest.sig.json"
BATCH_PATH = "out/normalized/batch.json"
PUBKEY_PATH = "tests/fixtures/crypto/test_ed25519_pub.pem"
PRIVKEY_PATH = "tests/fixtures/crypto/test_ed25519_priv.pem"
DEFAULT_DOMAIN_TAG = "tm.s7.batch.v1"
SCHEMA_VERSION = "1"

@dataclass(slots=True)
class SignBatchError(RuntimeError):
    message: str
    exit_code: int = 52

    def __str__(self) -> str:  # pragma: no cover - dataclass repr override
        return self.message


def _read_json(path: Path) -> Mapping[str, Any]:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:  # pragma: no cover - defensive
        raise SignBatchError(f"batch not found: {path}") from exc
    except json.JSONDecodeError as exc:  # pragma: no cover - defensive
        raise SignBatchError(f"invalid json: {path}") from exc


def _extract_pem_bytes(path: Path, header: str) -> bytes:
    text = path.read_text(encoding="utf-8").strip()
    lines: Iterable[str] = []
    capture = False
    chunks: list[str] = []
    for line in text.splitlines():
        line = line.strip()
        if not line:
            continue
        if line.startswith("-----BEGIN"):
            capture = line == header
            continue
        if line.startswith("-----END"):
            break
        if capture:
            chunks.append(line)
    if not chunks:
        raise SignBatchError(f"missing PEM body for {header}")
    try:
        return base64.b64decode("".join(chunks), validate=True)
    except Exception as exc:  # pragma: no cover - defensive
        raise SignBatchError("invalid base64 in PEM") from exc


def _load_private_key(path: Path) -> signing.SigningKey:
    raw = _extract_pem_bytes(path, "-----BEGIN ED25519 PRIVATE KEY-----")
    if len(raw) not in (32, 64):
        raise SignBatchError("ed25519 private key must be 32 or 64 bytes")
    seed = raw[:32]
    return signing.SigningKey(seed)


def _load_public_key(path: Path) -> bytes:
    raw = _extract_pem_bytes(path, "-----BEGIN ED25519 PUBLIC KEY-----")
    if len(raw) != 32:
        raise SignBatchError("ed25519 public key must be 32 bytes")
    return raw


def _canonical_payload(batch: Mapping[str, Any]) -> Mapping[str, Any]:
    required = ("root", "entries_hash", "schema_version", "created_at")
    missing = [key for key in required if key not in batch]
    if missing:
        raise SignBatchError(f"missing fields in batch: {', '.join(missing)}")
    schema_version = str(batch["schema_version"])
    if schema_version != SCHEMA_VERSION:
        raise SignBatchError(
            f"unsupported schema_version: {schema_version}", exit_code=52
        )
    return {
        "created_at": batch["created_at"],
        "entries_hash": batch["entries_hash"],
        "root": batch["root"],
        "schema_version": schema_version,
    }


def _canonical_bytes(payload: Mapping[str, Any]) -> bytes:
    return json.dumps(payload, separators=(",", ":"), sort_keys=True).encode("utf-8")


def _ensure_parent(path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)


def sign_batch(
    batch_path: Path | None = None,
    *,
    out_path: Path | None = None,
    privkey_path: Path | None = None,
    pubkey_path: Path | None = None,
    domain_tag: str = DEFAULT_DOMAIN_TAG,
) -> Path:
    batch_path = Path(batch_path or BATCH_PATH)
    out_path = Path(out_path or SIGNATURE_PATH)
    privkey_path = Path(privkey_path or PRIVKEY_PATH)
    pubkey_path = Path(pubkey_path or PUBKEY_PATH)

    batch_data = _read_json(batch_path)
    payload = _canonical_payload(batch_data)
    payload_bytes = _canonical_bytes(payload)

    domain = (domain_tag if domain_tag.endswith("\n") else domain_tag + "\n").encode(
        "utf-8"
    )

    signing_key = _load_private_key(privkey_path)
    verify_key = signing_key.verify_key
    expected_public = _load_public_key(pubkey_path)
    if bytes(verify_key) != expected_public:
        raise SignBatchError(
            "public key mismatch between private key and fixture",
            exit_code=52,
        )

    message = domain + payload_bytes
    signature = signing_key.sign(message).signature
    try:
        signing.VerifyKey(expected_public).verify(message, signature)
    except nacl_exceptions.BadSignatureError as exc:
        raise SignBatchError("self verification failed", exit_code=51) from exc

    batch_bytes = batch_path.read_bytes()
    signature_doc = {
        "batch_sha256": hashlib.sha256(batch_bytes).hexdigest(),
        "domain_tag": domain.decode("utf-8"),
        "payload": payload,
        "payload_sha256": hashlib.sha256(payload_bytes).hexdigest(),
        "public_key": base64.b64encode(expected_public).decode("ascii"),
        "schema_version": SCHEMA_VERSION,
        "signature": base64.b64encode(signature).decode("ascii"),
        "signed_at": dt.datetime.now(dt.UTC)
        .isoformat(timespec="seconds")
        .replace("+00:00", "Z"),
    }

    _ensure_parent(out_path)
    out_path.write_text(
        json.dumps(signature_doc, separators=(",", ":"), sort_keys=True),
        encoding="utf-8",
    )
    return out_path


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Sign canonical batch payload")
    parser.add_argument("--in", dest="batch", default=str(BATCH_PATH))
    parser.add_argument("--out", dest="out", default=str(SIGNATURE_PATH))
    parser.add_argument("--privkey", dest="privkey", default=str(PRIVKEY_PATH))
    parser.add_argument("--pubkey", dest="pubkey", default=str(PUBKEY_PATH))
    parser.add_argument("--domain-tag", dest="domain_tag", default=DEFAULT_DOMAIN_TAG)
    return parser


def main(argv: Iterable[str] | None = None) -> int:
    parser = _build_parser()
    args = parser.parse_args(list(argv) if argv is not None else None)
    try:
        sign_batch(
            Path(args.batch),
            out_path=Path(args.out),
            privkey_path=Path(args.privkey),
            pubkey_path=Path(args.pubkey),
            domain_tag=args.domain_tag,
        )
    except SignBatchError as exc:
        payload = {"ok": False, "error": exc.message}
        print(json.dumps(payload, separators=(",", ":"), sort_keys=True), flush=True)
        return exc.exit_code
    return 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
