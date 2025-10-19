#!/usr/bin/env bash
set -euo pipefail

ROOT=$(git rev-parse --show-toplevel)
OUT_DIR="$ROOT/out/s4_orr"
BUNDLE_ROOT="$ROOT/out"
TIMESTAMP=$(date -u +%Y%m%dT%H%M%SZ)
BUNDLE="$BUNDLE_ROOT/s4_evidence_bundle_${TIMESTAMP}.zip"
SHA_FILE="$BUNDLE.sha256"

mkdir -p "$OUT_DIR" "$BUNDLE_ROOT"

log() {
  printf '[bundle] %s\n' "$1"
}

EVIDENCES=(
  "$OUT_DIR/dec_120rps_60m.json"
  "$OUT_DIR/EVI/dec_p95_seconds_5m.json"
  "$OUT_DIR/EVI/cdc_lag_p95_seconds_5m.json"
  "$OUT_DIR/EVI/web_inp_snapshot.json"
  "$OUT_DIR/EVI/schema_compat.log"
  "$OUT_DIR/EVI/gitleaks.json"
  "$OUT_DIR/EVI/trivy.json"
  "$OUT_DIR/EVI/governance.json"
  "$ROOT/docs/spec/invariants.md"
  "$ROOT/docs/spec/tla/dec_pre_ga.tla"
  "$ROOT/docs/ADRs"
  "$ROOT/ops/prom"
  "$ROOT/docs/runbooks"
)

TMP_LIST=$(mktemp)
>"$TMP_LIST"
for item in "${EVIDENCES[@]}"; do
  if [ -e "$item" ]; then
    log "Adicionando $item"
    if [ -d "$item" ]; then
      find "$item" -type f -print >> "$TMP_LIST"
    else
      printf '%s\n' "$item" >> "$TMP_LIST"
    fi
  else
    log "Aviso: artefato não encontrado $item"
  fi
done

log "Compactando evidências"
zip -@ "$BUNDLE" < "$TMP_LIST"
rm "$TMP_LIST"

log "Calculando SHA-256"
sha256sum "$BUNDLE" | tee "$SHA_FILE"

log "Bundle gerado em $BUNDLE"
