#!/usr/bin/env bash
set -euo pipefail
# 1) Bloqueia caracteres nao-ASCII nas specs
if LC_ALL=C grep -n "[^[:ascii:]]" -r docs/spec/tla; then
  echo "[tla-ascii-guard] Non-ASCII encontrado (use /\\, \\/ e \\*)" >&2
  exit 1
fi
# 2) Garante que comentarios comecam com \\* (nunca com * no inicio de linha)
if grep -n "^[[:space:]]\* " -r docs/spec/tla; then
  echo "[tla-ascii-guard] Comentarios devem iniciar com \\\\* (backslash+asterisk)." >&2
  exit 1
fi
