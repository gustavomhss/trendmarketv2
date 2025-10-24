#!/usr/bin/env bash
set -euo pipefail

echo "[microbench] Rodando cargo bench (Criterion)"
export RUSTFLAGS="${RUSTFLAGS:-} -C target-cpu=native"
export CARGO_TERM_COLOR=always

if ! command -v cargo >/dev/null 2>&1; then
  echo "[microbench] ERRO: cargo não encontrado no PATH" >&2
  exit 101
fi

cargo bench --quiet || true

THRESHOLDS_FILE="ops/microbench_thresholds.json"
if [ ! -f "$THRESHOLDS_FILE" ]; then
  echo "[microbench] ERRO: $THRESHOLDS_FILE não encontrado" >&2
  exit 101
fi

violations=()

while IFS= read -r bench; do
  name=$(echo "$bench" | tr -d '\r')
  est_file="target/criterion/${name}/new/estimates.json"
  if [ ! -f "$est_file" ]; then
    echo "[microbench] ERRO: resultado ausente para benchmark '${name}' em ${est_file}" >&2
    violations+=("${name}:missing")
    continue
  fi
  mean=$(jq -r '.mean.point_estimate' "$est_file")
  max_mean=$(jq -r --arg n "$name" '.[$n].mean_ns' "$THRESHOLDS_FILE")
  if [ "$max_mean" = "null" ] || [ -z "$max_mean" ]; then
    echo "[microbench] ERRO: limiar mean_ns ausente p/ '${name}' em ${THRESHOLDS_FILE}" >&2
    violations+=("${name}:no-threshold")
    continue
  fi
  printf '[microbench] %-12s mean=%10.0f ns  threshold=%10d ns\n' "$name" "$mean" "$max_mean"
  awk "BEGIN {exit !($mean > $max_mean)}" && {
    echo "[microbench] VIOLAÇÃO: '${name}' mean ${mean}ns > ${max_mean}ns" >&2
    violations+=("${name}:mean>${max_mean}")
  } || true

done < <(jq -r 'keys[]' "$THRESHOLDS_FILE")

if [ ${#violations[@]} -gt 0 ]; then
  echo "[microbench] Falhou. Violações:" >&2
  for v in "${violations[@]}"; do echo " - $v" >&2; done
  exit 101
fi

echo "[microbench] Todos os limiares atendidos"
