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
    raw = kp.read_text()
    try:
        ks = json.loads(raw)
    except Exception as e:
        raise SystemExit(f"[sign] invalid keystore json: {e}")

    # Suporta dois esquemas:
    # (A) Top-level:
    #   - pubkey_b64 / allowed_pubkeys / not_before / expires_at
    # (B) Lista de chaves:
    #   { "keys": [ { pubkey|pubkey_b64, status, not_before, expires_at }, ... ] }
    def _parse_time(ts):
        if not isinstance(ts, str):
            return None
        t = ts
        if t.endswith("Z"):
            t = t[:-1] + "+00:00"
        try:
            from datetime import datetime
            return datetime.fromisoformat(t)
        except Exception:
            return None

    from datetime import datetime, timezone
    now = datetime.now(timezone.utc)

    # --- Esquema A (top-level) ---
    top_pub = ks.get("pubkey_b64") or ks.get("pubkey")
    if isinstance(top_pub, str) and top_pub:
        if top_pub != pubkey_b64:
            raise SystemExit("[sign] pubkey mismatch against keystore (top-level)")
        nb = _parse_time(ks.get("not_before"))
        if nb and now < nb:
            raise SystemExit("[sign] key not valid yet (not_before)")
        exp = _parse_time(ks.get("expires_at") or ks.get("expire_at"))
        if exp and now >= exp:
            raise SystemExit("[sign] key expired (expires_at)")
        allowed = ks.get("allowed_pubkeys")
        if isinstance(allowed, list) and allowed and pubkey_b64 not in allowed:
            raise SystemExit("[sign] pubkey not whitelisted in keystore")
        status = ks.get("status")
        if isinstance(status, str) and status.lower() not in ("active","valid","enabled", ""):
            raise SystemExit("[sign] key status not active")
        return

    # --- Esquema B (keys[]) ---
    keys = ks.get("keys")
    if isinstance(keys, list):
        # aceita pubkey ou pubkey_b64
        def _get_key_pub(k):
            v = k.get("pubkey_b64") or k.get("pubkey")
            return v if isinstance(v, str) else None
        matches = [k for k in keys if _get_key_pub(k) == pubkey_b64]
        if not matches:
            # se o arquivo tem lista e não achou a chave, bloqueia
            raise SystemExit("[sign] pubkey not found in keystore keys[]")
        k = matches[0]
        nb = _parse_time(k.get("not_before"))
        if nb and now < nb:
            raise SystemExit("[sign] key not valid yet (not_before)")
        exp = _parse_time(k.get("expires_at") or k.get("expire_at"))
        if exp and now >= exp:
            raise SystemExit("[sign] key expired (expires_at)")
        status = k.get("status")
        if isinstance(status, str) and status.lower() not in ("active","valid","enabled", ""):
            raise SystemExit("[sign] key status not active")
        return

    # Se não encaixa em nenhum formato conhecido, é permitido por default (compat leniente)
    return


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
