#!/usr/bin/env bash
set -euo pipefail

log() {
  printf '[tla-ascii-guard] %s\n' "$1" >&2
}

ROOT=$(git rev-parse --show-toplevel)
cd "$ROOT"

REPORT="$ROOT/out/s4_orr/tla_ascii_report.txt"
mkdir -p "$(dirname "$REPORT")"

mapfile -t TLA_FILES < <(git ls-files -- '*.tla' || true)

if (( ${#TLA_FILES[@]} == 0 )); then
  {
    printf '# tla_ascii_guard report\n'
    printf 'No tracked .tla files found.\n'
  } > "$REPORT"
  log "Nenhum arquivo .tla encontrado — nada a verificar."
  exit 0
fi

ASCII_FAILURE=0
COMMENT_FAILURE=0
declare -a ASCII_FILES=()

generate_report() {
  ASCII_FILES=()
  ASCII_FAILURE=0
  COMMENT_FAILURE=0

  {
    printf '# tla_ascii_guard report\n\n'
    printf 'Tracked .tla files (%d):\n' "${#TLA_FILES[@]}"
    for file in "${TLA_FILES[@]}"; do
      printf ' - %s\n' "$file"
    done
    printf '\n'
  } > "$REPORT"

  for file in "${TLA_FILES[@]}"; do
    local had_header=0
    local added_comment_header=0
    local -a hits=()
    local -a comment_hits=()

    mapfile -t hits < <(LC_ALL=C grep -n --color=never '[^[:print:][:space:]]' "$file" || true)
    if (( ${#hits[@]} > 0 )); then
      ASCII_FAILURE=1
      ASCII_FILES+=("$file")
      {
        printf '## Non-ASCII characters in %s\n' "$file"
        for hit in "${hits[@]}"; do
          printf '  %s\n' "$hit"
        done
        printf '\n'
      } >> "$REPORT"
      had_header=1
    fi

    mapfile -t comment_hits < <(LC_ALL=C grep -n --color=never '^[[:space:]]\* ' "$file" || true)
    if (( ${#comment_hits[@]} > 0 )); then
      COMMENT_FAILURE=1
      if (( had_header == 0 )); then
        printf '## Issues in %s\n' "$file" >> "$REPORT"
        had_header=1
      fi
      if (( added_comment_header == 0 )); then
        printf '  Invalid comment prefixes (expected \\*):\n' >> "$REPORT"
        added_comment_header=1
      fi
      for hit in "${comment_hits[@]}"; do
        printf '    %s\n' "$hit" >> "$REPORT"
      done
      printf '\n' >> "$REPORT"
    fi
  done

  {
    printf 'ASCII status: %s\n' "$([ "$ASCII_FAILURE" -eq 0 ] && echo OK || echo FAIL)"
    printf 'Comment status: %s\n' "$([ "$COMMENT_FAILURE" -eq 0 ] && echo OK || echo FAIL)"
  } >> "$REPORT"
}

generate_report

if (( ASCII_FAILURE == 0 && COMMENT_FAILURE == 0 )); then
  log "Todos os arquivos .tla estão em ASCII e com comentários válidos."
  exit 0
fi

if (( ASCII_FAILURE != 0 )) && [[ "${TLA_ASCII_FIX:-0}" != "0" ]]; then
  if ! command -v python3 >/dev/null 2>&1; then
    log "python3 é necessário para TLA_ASCII_FIX."
    exit 1
  fi
  log "TLA_ASCII_FIX habilitado — convertendo caracteres não-ASCII em escapes."
  for file in "${ASCII_FILES[@]}"; do
    python3 - "$file" <<'PY'
import pathlib
import sys

path = pathlib.Path(sys.argv[1])
text = path.read_text(encoding='utf-8')
converted = ''.join(c if ord(c) < 128 else '\\u%04X' % ord(c) for c in text)
path.write_text(converted, encoding='utf-8')
PY
  done
  generate_report
fi

if (( ASCII_FAILURE != 0 )); then
  log "Caracteres não-ASCII permanecem — consulte ${REPORT}."
  exit 2
fi

if (( COMMENT_FAILURE != 0 )); then
  log "Comentários inválidos encontrados — consulte ${REPORT}."
  exit 1
fi

log "Verificações concluídas sem pendências."
exit 0
