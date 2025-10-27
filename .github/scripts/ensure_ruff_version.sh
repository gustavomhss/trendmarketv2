#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(git rev-parse --show-toplevel 2>/dev/null || pwd)"
VER_FILE="$ROOT_DIR/.tools/ruff.version"
mkdir -p "$ROOT_DIR/.tools"

if [[ ! -f "$VER_FILE" ]]; then
  if command -v ruff >/dev/null 2>&1; then
    ruff --version | sed -E 's/^ruff ([0-9]+\.[0-9]+\.[0-9]+).*$/\1/' >"$VER_FILE"
  else
    python -m pip install --upgrade pip >/dev/null
    python -m pip install "ruff" >/dev/null
    ruff --version | sed -E 's/^ruff ([0-9]+\.[0-9]+\.[0-9]+).*$/\1/' >"$VER_FILE"
  fi
fi

REQ_VER="$(tr -d '\r\n' <"$VER_FILE")"
if [[ -z "$REQ_VER" ]]; then
  echo "[ensure-ruff] version file $VER_FILE is empty" >&2
  exit 1
fi

CURRENT_VER=""
if command -v ruff >/dev/null 2>&1; then
  CURRENT_VER=$(ruff --version | sed -E 's/^ruff ([0-9]+\.[0-9]+\.[0-9]+).*$/\1/')
fi
if [[ "$CURRENT_VER" != "$REQ_VER" ]]; then
  python -m pip install --upgrade "ruff==${REQ_VER}"
fi

ACT_VER=$(ruff --version | sed -E 's/^ruff ([0-9]+\.[0-9]+\.[0-9]+).*$/\1/')
if [[ "$ACT_VER" != "$REQ_VER" ]]; then
  echo "[ensure-ruff] version mismatch: have $ACT_VER want $REQ_VER" >&2
  exit 1
fi

echo "[ensure-ruff] using ruff ${ACT_VER}"
