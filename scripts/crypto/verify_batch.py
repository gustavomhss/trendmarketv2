from __future__ import annotations
import sys, json, base64, hashlib
from pathlib import Path
try:
    from nacl import signing
except Exception as e:
    sys.stderr.write(f"[verify] missing vendored nacl: {e}\n")
    sys.exit(5)

def _sha256_hex(path: Path) -> str:
    h = hashlib.sha256()
    with path.open('rb') as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b''):
            h.update(chunk)
    return h.hexdigest()

def _canon_manifest(manifest: list[dict]) -> bytes:
    lines = [f"{m['sha256']}  {m['path']}\n" for m in sorted(manifest, key=lambda m: m['path'])]
    return "".join(lines).encode("utf-8")

def verify(signature_json: Path) -> bool:
    data = json.loads(signature_json.read_text())
    pub = base64.b64decode(data["pubkey_b64"])
    sig = base64.b64decode(data["signature_b64"])
    manifest = data["manifest"]

    # valida hashes + existência
    for m in manifest:
        p = Path(m["path"])
        if not p.is_file() or _sha256_hex(p) != m["sha256"]:
            return False

    msg = _canon_manifest(manifest)
    vk = signing.VerifyKey(pub)
    try:
        vk.verify(msg, sig)
        return True
    except Exception:
        return False

def main(argv=None) -> int:
    argv = list(sys.argv[1:] if argv is None else argv)
    if not argv:
        sys.stderr.write("[verify] usage: verify_batch.py <signature.json>\n"); return 2
    ok = verify(Path(argv[0]))
    print("OK" if ok else "FAIL")
    return 0 if ok else 3

if __name__ == "__main__":
    raise SystemExit(main())
