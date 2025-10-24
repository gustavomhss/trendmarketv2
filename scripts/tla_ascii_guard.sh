#!/usr/bin/env bash
set -uo pipefail

shopt -s nullglob

files=(docs/spec/tla/*.tla *.tla)

declare -a targets=()
for candidate in "${files[@]}"; do
  [[ -f "$candidate" ]] && targets+=("$candidate")
done

if (( ${#targets[@]} == 0 )); then
  printf '[tla-ascii-guard] Nenhum arquivo .tla encontrado.\n' >&2
  exit 0
fi

exit_code=0

report_unicode() {
  local file="$1"
  shift
  exit_code=1
  printf '[tla-ascii-guard] Caracteres não ASCII detectados em %s:\n' "$file" >&2
  local hit
  for hit in "$@"; do
    printf '  %s\n' "$hit" >&2
  done
}

report_suspect() {
  local file="$1"
  local label="$2"
  shift 2
  exit_code=1
  printf '[tla-ascii-guard] Operador suspeito (%s) detectado em %s:\n' "$label" "$file" >&2
  local hit
  for hit in "$@"; do
    printf '  %s\n' "$hit" >&2
  done
}

declare -A suspect_patterns=(
  [$'\u2200']='∀ (FORALL)'
  [$'\u2203']='∃ (EXISTS)'
  [$'\u2227']='∧ (AND)'
  [$'\u2228']='∨ (OR)'
  [$'\u00ac']='¬ (NOT)'
  [$'\u2260']='≠ (NOT EQUAL)'
  [$'\u2264']='≤ (LESS OR EQUAL)'
  [$'\u2265']='≥ (GREATER OR EQUAL)'
  [$'\u2208']='∈ (IN)'
  [$'\u2209']='∉ (NOT IN)'
  [$'\u222a']='∪ (UNION)'
  [$'\u2229']='∩ (INTERSECTION)'
  [$'\u2192']='→ (IMPLIES)'
  [$'\u2194']='↔ (EQUIVALENCE)'
  [$'\u21a6']='↦ (MAPS TO)'
  [$'\u25a1']='□ (ALWAYS)'
  [$'\u25c7']='◇ (EVENTUALLY)'
  [$'\u25ca']='◊ (EVENTUALLY)'
  [$'\u2026']='… (ELLIPSIS)'
)

for file in "${targets[@]}"; do
  mapfile -t unicode_hits < <(LC_ALL=C grep -n $'[\200-\377]' "$file" || true)
  if (( ${#unicode_hits[@]} > 0 )); then
    report_unicode "$file" "${unicode_hits[@]}"
  fi

  for pattern in "${!suspect_patterns[@]}"; do
    mapfile -t suspect_hits < <(LC_ALL=C grep -nF -- "$pattern" "$file" || true)
    if (( ${#suspect_hits[@]} > 0 )); then
      report_suspect "$file" "${suspect_patterns[$pattern]}" "${suspect_hits[@]}"
    fi
  done

done

exit $exit_code
