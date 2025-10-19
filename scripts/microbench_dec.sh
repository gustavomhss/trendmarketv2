#!/usr/bin/env bash
set -euo pipefail

ROOT=$(git rev-parse --show-toplevel)
OUT_DIR="$ROOT/out/s4_orr"
mkdir -p "$OUT_DIR"

log() {
  printf '[microbench] %s\n' "$1"
}

COMMAND=${1:-run}
if [ "$COMMAND" = "--help" ]; then
  cat <<'USAGE'
Uso: scripts/microbench_dec.sh [--scenario dec_tail]
Executa benchmarks críticos do DEC e salva microbench.txt.
USAGE
  exit 0
fi

log "Executando cargo bench"
RUSTFLAGS="${RUSTFLAGS:-}" cargo bench --bench dec_paths -- --output-format bencher | tee "$OUT_DIR/microbench.txt"

if [ "${1:-}" = "--scenario" ] && [ "${2:-}" = "dec_tail" ]; then
  log "Registrando cenário de cauda p99"
  cargo bench --bench dec_paths -- --filter dec_tail --output-format bencher | tee -a "$OUT_DIR/microbench.txt"
fi

log "Benchmark concluído"
