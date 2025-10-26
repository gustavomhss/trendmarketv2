#!/usr/bin/env bash
set -euo pipefail

ROOT=$(git rev-parse --show-toplevel 2>/dev/null || pwd)
OUT_DIR="$ROOT/out/obs_gatecheck"
EVID_DIR="$OUT_DIR/evidence"
BUNDLE_TS=$(date -u +%Y%m%dT%H%M%SZ)
BUNDLE="$OUT_DIR/bundle_${BUNDLE_TS}.zip"
SHA_FILE="$OUT_DIR/bundle.sha256.txt"

log() {
  printf '[s5-bundle] %s\n' "$1"
}

if [ ! -d "$EVID_DIR" ]; then
  log "Evidence directory $EVID_DIR not found"
  exit 1
fi

TMP_LIST=$(mktemp)
find "$EVID_DIR" -type f | sort > "$TMP_LIST"

log "Creating bundle at $BUNDLE"
(cd "$OUT_DIR" && zip -@ "$(basename "$BUNDLE")" < "$TMP_LIST")
rm "$TMP_LIST"

log "Computing SHA-256"
( cd "$OUT_DIR" && sha256sum "$(basename "$BUNDLE")" ) | tee "$SHA_FILE"

log "Bundle ready"
