#!/usr/bin/env bash
set -euo pipefail
OUT="out/obs_gatecheck/evidence"
mkdir -p "$OUT"
python3 scripts/obs_sbom_generate.py "$OUT/sbom.cdx.json"
if command -v sha256sum >/dev/null 2>&1; then
  sha256sum "$OUT/sbom.cdx.json" > "$OUT/sbom.cdx.sha256"
else
  shasum -a 256 "$OUT/sbom.cdx.json" > "$OUT/sbom.cdx.sha256"
fi
echo SBOM_OK
