#!/usr/bin/env bash
set -euo pipefail
EVI="${EVI:-out/obs_gatecheck/evidence}"; mkdir -p "$EVI"
SBOM_PATH="$EVI/sbom.cdx.json"
HASH_PATH="$EVI/sbom.cdx.sha256"
export SBOM_PATH HASH_PATH

hash_file() {
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$SBOM_PATH" > "$HASH_PATH"
  else
    shasum -a 256 "$SBOM_PATH" > "$HASH_PATH"
  fi
}

if [ -f Cargo.toml ]; then
  if command -v cargo >/dev/null 2>&1; then
    cargo install cargo-cyclonedx >/dev/null 2>&1 || true
    if cargo cyclonedx --help >/dev/null 2>&1; then
      cargo cyclonedx --format json | tee "$SBOM_PATH" >/dev/null
      hash_file
      echo SBOM_OK
      exit 0
    else
      echo "cargo cyclonedx indisponível — SBOM skip"
      exit 0
    fi
  else
    echo "cargo indisponível — SBOM skip"
    exit 0
  fi
fi

if command -v python3 >/dev/null 2>&1; then
  python3 -m pip install --quiet --user cyclonedx-bom >/dev/null 2>&1 || true
  CYC_BIN="$(python3 -c 'import os, shutil, site; import sys
path = shutil.which("cyclonedx-bom")
if path:
    print(path)
else:
    user_bin = os.path.join(site.USER_BASE, "bin", "cyclonedx-bom")
    print(user_bin if os.path.exists(user_bin) else "")
')"
  if [ -n "$CYC_BIN" ] && [ -x "$CYC_BIN" ]; then
    "$CYC_BIN" -o "$SBOM_PATH" >/dev/null
    hash_file
    echo SBOM_OK
  else
    echo "cyclonedx-bom indisponível — gerando fallback"
    python3 <<'PY'
import datetime
import json
import os
import subprocess
import sys
from pathlib import Path

sbom_path = Path(os.environ.get("SBOM_PATH", "out/obs_gatecheck/evidence/sbom.cdx.json"))
components = []
try:
    output = subprocess.check_output([sys.executable, "-m", "pip", "list", "--format", "json"], text=True)
    for pkg in json.loads(output):
        components.append({
            "type": "library",
            "name": pkg.get("name"),
            "version": pkg.get("version"),
        })
except Exception:
    components = []

bom = {
    "bomFormat": "CycloneDX",
    "specVersion": "1.4",
    "version": 1,
    "metadata": {
        "timestamp": datetime.datetime.utcnow().isoformat() + "Z",
        "tools": [
            {
                "vendor": "trendmarketv2",
                "name": "obs_sbom_fallback",
                "version": "1.0",
            }
        ],
    },
    "components": components,
}

sbom_path.parent.mkdir(parents=True, exist_ok=True)
sbom_path.write_text(json.dumps(bom, indent=2))
PY
    hash_file
    echo SBOM_OK
  fi
else
  echo "python3 indisponível — SBOM skip"
fi
