#!/usr/bin/env bash
set -euo pipefail
OUT="out/obs_gatecheck"; EVI="$OUT/evidence"; LOG="$OUT/logs"; mkdir -p "$OUT"
( cd "$OUT" && zip -qr bundle.zip evidence logs || true )
if command -v sha256sum >/dev/null 2>&1; then sha256sum "$OUT/bundle.zip" > "$OUT/bundle.sha256.txt"; else shasum -a 256 "$OUT/bundle.zip" > "$OUT/bundle.sha256.txt"; fi
