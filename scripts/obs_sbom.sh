#!/usr/bin/env bash
set -euo pipefail
EVI="out/obs_gatecheck/evidence"; mkdir -p "$EVI"
if command -v cargo >/dev/null 2>&1; then
  cargo install cargo-cyclonedx >/dev/null 2>&1 || true
  if cargo cyclonedx --help >/dev/null 2>&1; then
    cargo cyclonedx --format json --output "$EVI/sbom.cdx.json"
    if command -v sha256sum >/dev/null 2>&1; then sha256sum "$EVI/sbom.cdx.json" > "$EVI/sbom.cdx.sha256"; else shasum -a 256 "$EVI/sbom.cdx.json" > "$EVI/sbom.cdx.sha256"; fi
    echo SBOM_OK
  else
    echo "cargo cyclonedx indisponível — SBOM skip"
  fi
else
  echo "cargo indisponível — SBOM skip"
fi
