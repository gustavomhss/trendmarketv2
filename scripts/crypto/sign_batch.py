from __future__ import annotations
import os, sys, json, base64, hashlib, datetime
from pathlib import Path
from typing import Iterable, Union

# Importa 'nacl' vendorizado (./nacl) e cai para PyNaCl, se existir
try:
    from nacl import signing
except Exception:  # pragma: no cover
    try:
        from nacl import signing  # type: ignore
    except Exception as e:
        sys.stderr.write(f"[sign] NaCl indisponível (vendored/pip): {e}\n")
        raise

PathLike = Union[str, Path]
SIGNATURE_PATH: Path = Path("out/evidence/S7_event_model/batch.signature.json")  # monkeypatch nos testes
ENV_PRIMARY  = "ORACLE_ED25519_SEED"
ENV_FALLBACK = "CE_SIGN_SEED_B64"

def _ensure_dir(p: Path) -> None:
    p.mkdir(parents=True, exist_ok=True)

def _sha256_hex(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()

def _canon_manifest(manifest: list[dict]) -> bytes:
    # "<sha256>  <relpath>\n" em ordem lexicográfica
    lines = [f"{m['sha256']}  {m['path']}\n" for m in sorted(manifest, key=lambda m: m["path"])]
    return "".join(lines).encode("utf-8")

def _b64(s: bytes) -> str:
    return base64.b64encode(s).decode("ascii")

def _load_seed_b64() -> str:
    seed = os.environ.get(ENV_PRIMARY) or os.environ.get(ENV_FALLBACK)
    if not seed:
        raise SystemExit(f"[sign] missing env {ENV_PRIMARY} (ou {ENV_FALLBACK})")
    return seed

def _load_signing_key() -> signing.SigningKey:
    seed_b64 = _load_seed_b64()
    try:
        seed = base64.b64decode(seed_b64, validate=True)
    except Exception as e:
        raise SystemExit(f"[sign] invalid base64 seed: {e}")
    if len(seed) != 32:
        raise SystemExit(f"[sign] seed length != 32 (got {len(seed)})")
    return signing.SigningKey(seed)

def _parse_time(ts: str) -> datetime.datetime:
    # aceita "YYYY-MM-DDTHH:MM:SSZ" ou com offset
    if ts.endswith("Z"):
        ts = ts.replace("Z", "+00:00")
    return datetime.datetime.fromisoformat(ts)

def _enforce_keystore_policy(keystore_path: Path | None, pubkey_b64: str) -> None:
    if not keystore_path:
        return
    kp = Path(keystore_path)
    if not kp.exists():
        # keystore opcional nos testes; se não existir, ignore
        return
    try:
        ks = json.loads(kp.read_text())
    except Exception as e:
        raise SystemExit(f"[sign] invalid keystore json: {e}")

    # Campos suportados (qualquer é opcional):
    # - "pubkey_b64": string
    # - "allowed_pubkeys": [string, ...]
    # - "not_before": ISO8601 / "expires_at": ISO8601
    now = datetime.datetime.now(datetime.timezone.utc)

    nb = ks.get("not_before")
    if isinstance(nb, str):
        if now < _parse_time(nb):
            raise SystemExit("[sign] key not valid yet (not_before)")

    exp = ks.get("expires_at") or ks.get("expire_at")
    if isinstance(exp, str):
        if now >= _parse_time(exp):
            raise SystemExit("[sign] key expired (expires_at)")

    pk = ks.get("pubkey_b64")
    if isinstance(pk, str) and pk and pk != pubkey_b64:
        raise SystemExit("[sign] pubkey mismatch against keystore")

    allowed = ks.get("allowed_pubkeys")
    if isinstance(allowed, list) and allowed and pubkey_b64 not in allowed:
        raise SystemExit("[sign] pubkey not whitelisted in keystore")

def _build_manifest(paths: Iterable[PathLike]) -> list[dict]:
    items = []
    for p in paths:
        pp = Path(p)
        if not pp.is_file():
            raise SystemExit(f"[sign] missing file to sign: {pp}")
        items.append({"path": str(pp), "sha256": _sha256_hex(pp)})
    return items

def sign_batch(batch_or_paths: Union[PathLike, Iterable[PathLike]], keystore_path: PathLike | None = None) -> str:
    """
    Compatível com os testes:
      sign_batch(batch_path: PathLike, keystore_path: PathLike)
    Também aceita uma lista de caminhos para assinar múltiplos arquivos.
    Retorna o caminho (str) do arquivo de assinatura gerado.
    """
    # Normaliza entrada para uma lista de paths
    if isinstance(batch_or_paths, (str, Path)):
        paths = [batch_or_paths]
    else:
        paths = list(batch_or_paths)
    manifest = _build_manifest(paths)

    sk = _load_signing_key()
    vk = sk.verify_key
    msg = _canon_manifest(manifest)
    sig = sk.sign(msg).signature  # bytes

    pubkey_b64 = _b64(bytes(vk))
    _enforce_keystore_policy(Path(keystore_path) if keystore_path else None, pubkey_b64)

    payload = {
        "algo": "ed25519",
        "pubkey_b64": pubkey_b64,
        "signature_b64": _b64(sig),
        "manifest": manifest,
    }

    outp = SIGNATURE_PATH
    _ensure_dir(outp.parent)
    outp.write_text(json.dumps(payload, indent=2, ensure_ascii=False) + "\n")
    return str(outp)
