#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR=$(git rev-parse --show-toplevel 2>/dev/null || pwd)
LOCK_ERR=0

log() {
  printf '[env.pin] %s\n' "$1"
}

require() {
  if ! command -v "$1" >/dev/null 2>&1; then
    log "Ferramenta obrigatória ausente: $1"
    exit 1
  fi
}

log "Verificando toolchain mínima"
require python3
python3 -c 'import sys; assert sys.version_info >= (3, 10), "Python >=3.10 requerido"; print(f"Python {sys.version.split()[0]}")'
require pip
require node
require npm
require jq
require git
require cargo

for lock in requirements.lock package-lock.json Cargo.lock; do
  if [ ! -f "$ROOT_DIR/$lock" ]; then
    log "Lockfile ausente: $lock"
    LOCK_ERR=1
  else
    sha=$(sha256sum "$ROOT_DIR/$lock" | cut -d' ' -f1)
    log "$lock @ $sha"
  fi
done

DOCKERFILE="$ROOT_DIR/ops/containers/orr.Dockerfile"
if [ ! -f "$DOCKERFILE" ]; then
  log "Dockerfile pinado ausente: ops/containers/orr.Dockerfile"
  LOCK_ERR=1
else
  if ! grep -Eq '@sha256:[a-f0-9]+' "$DOCKERFILE"; then
    log "Dockerfile precisa referenciar imagem com digest fixo"
    LOCK_ERR=1
  fi
fi

if [ "$LOCK_ERR" -ne 0 ]; then
  log "Falha na validação de locks/digests"
  exit 2
fi

log "Locks e toolchain validados"
