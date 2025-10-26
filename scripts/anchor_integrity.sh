#!/usr/bin/env bash
set -euo pipefail

ROOT=$(git rev-parse --show-toplevel)
OUT_DIR="$ROOT/out/s4_orr"
EVI_DIR="$OUT_DIR/EVI"
mkdir -p "$EVI_DIR"

log() {
  printf '[anchor] %s\n' "$1"
}

FILES=(
  "$ROOT/docs/spec/invariants.md"
  "$ROOT/docs/spec/tla/dec_pre_ga.tla"
  "$ROOT/docs/ADRs"
  "$ROOT/obs/ops/prom"
  "$ROOT/docs/runbooks"
  "$ROOT/data/analytics/dbt/models/mbp/schema.yml"
  "$ROOT/data/cdc/schemas/mbp/quotes/v1.2.0.json"
  "$OUT_DIR/EVI"
)

JSON=$("$ROOT/scripts/anchor_root.py" "${FILES[@]}")
if ! command -v jq >/dev/null 2>&1; then
  log "jq é necessário para processar ANCHOR_ROOT"
  exit 1
fi
ROOT_HASH=$(echo "$JSON" | jq -r .root)
if [ -z "$ROOT_HASH" ] || [ "$ROOT_HASH" = "null" ]; then
  log "Falha ao calcular ANCHOR_ROOT"
  exit 1
fi

printf '%s\n' "$JSON" > "$OUT_DIR/ANCHOR.json"
printf '%s\n' "$ROOT_HASH" > "$OUT_DIR/ANCHOR.txt"
TAG="anchor-M2-$ROOT_HASH"
if git rev-parse "$TAG" >/dev/null 2>&1; then
  log "Tag já existe: $TAG"
else
  git tag -a "$TAG" -m "Evidence anchor M2"
  log "Tag criada: $TAG"
fi

log "ANCHOR_ROOT=$ROOT_HASH"
