#!/usr/bin/env bash
set -euo pipefail

ROOT=$(git rev-parse --show-toplevel)
ENGINE_DIR="$ROOT/engine"
OUT_DIR="$ROOT/out/s4_orr"
mkdir -p "$OUT_DIR"

log() {
  printf '[flame] %s\n' "$1"
}

require() {
  if ! command -v "$1" >/dev/null 2>&1; then
    log "Ferramenta necessária ausente: $1"
    exit 1
  fi
}

require cargo
pushd "$ENGINE_DIR" >/dev/null
if ! cargo flamegraph --help >/dev/null 2>&1; then
  log "cargo-flamegraph não disponível; instale com 'cargo install flamegraph'"
  popd >/dev/null
  exit 1
fi
if ! command -v perf >/dev/null 2>&1; then
  log "perf não encontrado; certifique-se de instalar para flamegraphs de kernel"
fi
if ! command -v inferno-flamegraph >/dev/null 2>&1 && ! command -v flamegraph.pl >/dev/null 2>&1; then
  log "inferno-flamegraph não encontrado; cargo-flamegraph deve puxar dependência"
fi

SVG_MAIN="$OUT_DIR/dec_flame.svg"
SVG_TAIL="$OUT_DIR/dec_flame_p99.svg"

log "Gerando flamegraph principal (dec_paths)"
CARGO_PROFILE=release cargo flamegraph --bench dec_paths --output "$SVG_MAIN"

log "Gerando flamegraph p99 (cenário dec_tail)"
CARGO_PROFILE=release cargo flamegraph --bench dec_paths --output "$SVG_TAIL" -- --scenario dec_tail

popd >/dev/null
