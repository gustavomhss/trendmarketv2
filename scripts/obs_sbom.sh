#!/usr/bin/env bash
set -euo pipefail

ROOT="$(git rev-parse --show-toplevel 2>/dev/null || pwd)"
EVI="$ROOT/out/obs_gatecheck/evidence"
mkdir -p "$EVI"

SBOM_JSON="$EVI/sbom.cdx.json"
SBOM_SHA="$EVI/sbom.cdx.sha256"

generate_with_cargo() {
  local manifest="$ROOT/Cargo.toml"
  if [[ ! -f "$manifest" ]]; then
    return 1
  fi
  if ! command -v cargo >/dev/null 2>&1; then
    return 1
  fi
  if ! cargo cyclonedx --help >/dev/null 2>&1; then
    cargo install cargo-cyclonedx >/dev/null 2>&1 || true
  fi
  if ! cargo cyclonedx --help >/dev/null 2>&1; then
    return 1
  fi

  local tmp="${SBOM_JSON}.tmp"
  if ! cargo cyclonedx --format json >"$tmp"; then
    rm -f "$tmp"
    return 1
  fi
  mv "$tmp" "$SBOM_JSON"
  return 0
}

generate_fallback() {
  if ! command -v python3 >/dev/null 2>&1; then
    echo "SBOM fallback requires python3" >&2
    return 1
  fi

  local tmp="${SBOM_JSON}.tmp"
  local py_file
  py_file="$(mktemp "${TMPDIR:-/tmp}/obs-sbom-XXXXXX.py")"

  trap 'rm -f "$py_file"' RETURN

  cat <<'PY' >"$py_file"
import hashlib
import json
import os
import subprocess
import uuid
from datetime import datetime, timezone
from pathlib import Path


def git_rev(repo_root: Path) -> str:
    try:
        result = subprocess.check_output(
            ["git", "rev-parse", "HEAD"],
            cwd=str(repo_root),
            stderr=subprocess.DEVNULL,
        )
        return result.decode().strip()
    except Exception:
        return datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")


def iter_components(repo_root: Path):
    include = ("src", "scripts", "ops", "docs/obs")
    for folder in include:
        base = repo_root / folder
        if not base.exists():
            continue
        for path in sorted(base.rglob("*")):
            if not path.is_file():
                continue
            rel = path.relative_to(repo_root).as_posix()
            if "/." in f"/{rel}":
                continue
            digest = hashlib.sha256(path.read_bytes()).hexdigest()
            yield {
                "bom-ref": f"file:{rel}",
                "type": "file",
                "name": rel,
                "hashes": [
                    {
                        "alg": "SHA-256",
                        "content": digest,
                    }
                ],
            }


def build_sbom(repo_root: Path) -> dict:
    return {
        "bomFormat": "CycloneDX",
        "specVersion": "1.4",
        "serialNumber": f"urn:uuid:{uuid.uuid4()}",
        "version": 1,
        "metadata": {
            "timestamp": datetime.now(timezone.utc)
            .isoformat()
            .replace("+00:00", "Z"),
            "tools": [
                {
                    "vendor": "trendmarketv2",
                    "name": "obs_sbom.sh fallback",
                    "version": "1.0",
                }
            ],
            "component": {
                "bom-ref": f"app:{repo_root.name}",
                "type": "application",
                "name": repo_root.name,
                "version": git_rev(repo_root),
            },
        },
        "components": list(iter_components(repo_root)),
    }


def main() -> None:
    repo_root = Path(os.environ["REPO_ROOT"]).resolve()
    sbom_path = Path(os.environ["SBOM_OUTPUT"]).resolve()
    sbom = build_sbom(repo_root)
    sbom_path.write_text(json.dumps(sbom, indent=2), encoding="utf-8")


if __name__ == "__main__":
    main()
PY

  REPO_ROOT="$ROOT" SBOM_OUTPUT="$tmp" python3 "$py_file"
  mv "$tmp" "$SBOM_JSON"
  trap - RETURN
  rm -f "$py_file"
}

write_sha256() {
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$SBOM_JSON" >"$SBOM_SHA"
    return
  fi
  if command -v shasum >/dev/null 2>&1; then
    shasum -a 256 "$SBOM_JSON" >"$SBOM_SHA"
    return
  fi

  local py_file
  py_file="$(mktemp)"

  cat >"$py_file" <<'PY'
import hashlib
import os
from pathlib import Path


sbom_path = Path(os.environ["SBOM_INPUT"]).resolve()
sha_path = Path(os.environ["SHA_OUTPUT"]).resolve()

digest = hashlib.sha256(sbom_path.read_bytes()).hexdigest()
sha_path.write_text(f"{digest}  {sbom_path.name}\n", encoding="utf-8")
PY

  SBOM_INPUT="$SBOM_JSON" SHA_OUTPUT="$SBOM_SHA" python3 "$py_file"
  rm -f "$py_file"
}

main() {
  rm -f "$SBOM_JSON" "$SBOM_SHA"

  if ! generate_with_cargo; then
    generate_fallback
  fi

  write_sha256

  echo SBOM_OK
}

main "$@"
