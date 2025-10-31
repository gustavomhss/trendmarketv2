from __future__ import annotations
import json, base64, hashlib, sys
from pathlib import Path

# usa 'nacl' vendorizado (./nacl) e cai para o PyNaCl, se existir
try:
    from nacl import signing, exceptions as n_ex
except Exception:
    try:
        from nacl import signing, exceptions as n_ex
    except Exception as e:
        sys.stderr.write(f"[verify] NaCl indisponível (vendored/pip): {e}\n")
        raise

class VerificationError(Exception):
    """Falha de verificação criptográfica ou de integridade."""

def _sha256_hex(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()

def _canon_manifest(manifest: list[dict]) -> bytes:
    # mesma canonicalização do sign_batch: "<sha256>  <relpath>\n" em ordem lexicográfica
    lines = [f"{m['sha256']}  {m['path']}\n" for m in sorted(manifest, key=lambda m: m["path"])]
    return "".join(lines).encode("utf-8")

def verify_signature(signature_path: str | Path) -> bool:
    sp = Path(signature_path)
    if not sp.is_file():
        raise VerificationError(f"signature file not found: {sp}")

    try:
        data = json.loads(sp.read_text())
    except Exception as e:
        raise VerificationError(f"invalid signature json: {e}")

    if data.get("algo") != "ed25519":
        raise VerificationError(f"unsupported algo: {data.get('algo')}")

    try:
        pub_b = base64.b64decode(data["pubkey_b64"], validate=True)
        sig_b = base64.b64decode(data["signature_b64"], validate=True)
    except Exception as e:
        raise VerificationError(f"invalid b64 fields: {e}")

    manifest = data.get("manifest") or []
    if not isinstance(manifest, list) or not manifest:
        raise VerificationError("empty or invalid manifest")

    # valida existência e hash dos arquivos
    for m in manifest:
        p = Path(m["path"])
        if not p.is_file():
            raise VerificationError(f"missing file: {p}")
        if _sha256_hex(p) != m["sha256"]:
            raise VerificationError(f"sha256 mismatch: {p}")

    msg = _canon_manifest(manifest)
    try:
        vk = signing.VerifyKey(pub_b)
        vk.verify(msg, sig_b)
    except Exception as e:
        # PyNaCl usa BadSignatureError; vendored também; tratamos genericamente
        raise VerificationError(f"bad signature: {e}")

    return True
