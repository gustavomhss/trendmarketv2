#!/usr/bin/env bash
set -euo pipefail

ROOT=$(git rev-parse --show-toplevel 2>/dev/null || pwd)
OUT_DIR="$ROOT/out"
mkdir -p "$OUT_DIR"
STAMP=$(date +%Y%m%d_%H%M%S)
BUNDLE="$OUT_DIR/s4_evidence_bundle_${STAMP}.zip"

log() {
  printf '[bundle] %s\n' "$1"
}

shopt -s nullglob
pushd "$ROOT" >/dev/null

CANDIDATES=(
  "out/s4_orr"
  "out/pip-audit"
  "data/analytics/dbt/target"
  "docs/ADRs/ADR-001-DEC-SLO-Degrade-Rollback.md"
  "docs/ADRs/ADR-002-Resolution-Engine-Regra.md"
  "docs/ADRs/ADR-003-TWAP-Benchmarks.md"
  "docs/runbooks"
  "obs/ops/watchers.yml"
  "scripts/microbench_dec.sh"
  "engine/benches"
)

ENTRIES=()
for pattern in "${CANDIDATES[@]}"; do
  matches=( $pattern )
  if [ ${#matches[@]} -eq 0 ]; then
    log "WARN: ${pattern} não encontrado"
    continue
  fi
  for match in "${matches[@]}"; do
    log "Incluindo ${match}"
    ENTRIES+=("${match}")
  done
done

if [ ${#ENTRIES[@]} -eq 0 ]; then
  log "Nenhuma evidência encontrada; criando pacote vazio"
  python3 - "$BUNDLE" <<'PY'
import sys
from zipfile import ZipFile

with ZipFile(sys.argv[1], 'w') as bundle:
    bundle.writestr('README.txt', 'Bundle gerado sem entradas disponíveis.')
PY
else
  zip -rq "$BUNDLE" "${ENTRIES[@]}"
fi

popd >/dev/null
shopt -u nullglob

log "Pacote gerado em ${BUNDLE}"
