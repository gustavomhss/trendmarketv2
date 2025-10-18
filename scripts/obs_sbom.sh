#!/usr/bin/env bash
set -euo pipefail
OUT="out/obs_gatecheck/evidence"; mkdir -p "$OUT"
if command -v cargo >/dev/null 2>&1; then
  cargo install cargo-cyclonedx >/dev/null 2>&1 || true
  if cargo cyclonedx --help >/dev/null 2>&1; then
    cargo cyclonedx --format json | tee "$OUT/sbom.cdx.json" >/dev/null
    if command -v sha256sum >/dev/null 2>&1; then sha256sum "$OUT/sbom.cdx.json" > "$OUT/sbom.cdx.sha256"; else shasum -a 256 "$OUT/sbom.cdx.json" > "$OUT/sbom.cdx.sha256"; fi
    echo SBOM_OK
  else
    echo "cargo cyclonedx indisponível — SBOM skip"
  fi
else
  echo "cargo indisponível — SBOM skip"
fi
