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

  tmp="${SBOM_JSON}.tmp"
  if ! cargo cyclonedx --format json >"$tmp"; then
    rm -f "$tmp"
    return 1
  fi
  mv "$tmp" "$SBOM_JSON"
  return 0
}

generate_fallback() {
  tmp="${SBOM_JSON}.tmp"
  ROOT="$ROOT" SBOM_JSON="$tmp" python3 - <<'PY'
import hashlib
import json
import os
import subprocess
import sys
import uuid
from datetime import datetime, timezone
from pathlib import Path

root = Path(os.environ["ROOT"]).resolve()
sbom_json = Path(os.environ["SBOM_JSON"]).resolve()

def git_rev() -> str:
    try:
        result = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=root, stderr=subprocess.DEVNULL
        )
        return result.decode().strip()
    except Exception:
        return datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")

def file_components() -> list[dict[str, object]]:
    include = ["src", "scripts", "ops", "docs/obs"]
    components: list[dict[str, object]] = []
    for folder in include:
        base = root / folder
        if not base.exists():
            continue
        for path in sorted(base.rglob("*")):
            if not path.is_file():
                continue
            rel = path.relative_to(root).as_posix()
            if "/." in f"/{rel}":
                continue
            digest = hashlib.sha256(path.read_bytes()).hexdigest()
            components.append(
                {
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
            )
    return components


sbom = {
    "bomFormat": "CycloneDX",
    "specVersion": "1.4",
    "serialNumber": f"urn:uuid:{uuid.uuid4()}",
    "version": 1,
    "metadata": {
        "timestamp": datetime.now(timezone.utc).isoformat().replace("+00:00", "Z"),
        "tools": [
            {
                "vendor": "trendmarketv2",
                "name": "obs_sbom.sh fallback",
                "version": "1.0",
            }
        ],
        "component": {
            "bom-ref": f"app:{root.name}",
            "type": "application",
            "name": root.name,
            "version": git_rev(),
        },
    },
    "components": file_components(),
}

sbom_json.write_text(json.dumps(sbom, indent=2), encoding="utf-8")
PY
  mv "$tmp" "$SBOM_JSON"
}

if ! generate_with_cargo; then
  generate_fallback
fi

if command -v sha256sum >/dev/null 2>&1; then
  sha256sum "$SBOM_JSON" >"$SBOM_SHA"
else
  shasum -a 256 "$SBOM_JSON" >"$SBOM_SHA"
fi

echo SBOM_OK
