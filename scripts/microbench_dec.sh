#!/usr/bin/env bash
set -euo pipefail

ROOT=$(git rev-parse --show-toplevel 2>/dev/null || pwd)
LOG_DIR="$ROOT/out/s4_orr/logs"
mkdir -p "$LOG_DIR"

log() {
  printf '[microbench] %s\n' "$1"
}

if ! command -v cargo >/dev/null 2>&1; then
  log "cargo não encontrado; ignorando microbench"
  exit 0
fi

if [ ! -f "$ROOT/Cargo.toml" ]; then
  log "Cargo.toml ausente; ignorando microbench"
  exit 0
fi

if [ ! -d "$ROOT/benches" ] || [ -z "$(find "$ROOT/benches" -maxdepth 1 -name '*.rs' -print -quit)" ]; then
  log "Nenhum bench Criterion detectado; ignorando microbench"
  exit 0
fi

LIST_FILE="$LOG_DIR/microbench_list.txt"
log "Descobrindo benchmarks disponíveis"
if ! cargo bench -- --list | tee "$LIST_FILE"; then
  if grep -q "no benchmark targets" "$LIST_FILE" 2>/dev/null; then
    log "Nenhum alvo de benchmark encontrado; ignorando"
    exit 0
  fi
  log "Falha ao listar benchmarks"
  exit 1
fi

if ! grep -Eq 'match_core|route_fast|twap_update' "$LIST_FILE"; then
  log "Benchmarks DEC não encontrados; ignorando execução"
  exit 0
fi

LOG_FILE="$LOG_DIR/microbench.txt"
log "Executando cargo bench"
cargo bench --bench dec_benches | tee "$LOG_FILE"

python3 - "$LOG_FILE" <<'PY'
import re
import sys
from pathlib import Path

log_path = Path(sys.argv[1])
text = log_path.read_text().splitlines()
pattern = re.compile(
    r'^(?P<name>[\w:.-]+)\s+time:\s+\[(?P<low>[-\d\.]+)\s*(?P<low_unit>ns|us|ms|s)\s+'
    r'(?P<med>[-\d\.]+)\s*(?P<med_unit>ns|us|ms|s)\s+(?P<high>[-\d\.]+)\s*(?P<high_unit>ns|us|ms|s)\]'
)
UNIT_TO_MS = {"s": 1000.0, "ms": 1.0, "us": 0.001, "ns": 0.000001}
bench_values = {}
for line in text:
    match = pattern.match(line.strip())
    if not match:
        continue
    name = match.group('name')
    median = float(match.group('med')) * UNIT_TO_MS[match.group('med_unit')]
    bench_values[name] = median

thresholds = {
    'match_core': 1.20,
    'route_fast': 0.70,
    'twap_update': 0.45,
}
failures = []
for label, limit in thresholds.items():
    candidates = {name: value for name, value in bench_values.items() if label in name}
    if not candidates:
        print(f"[microbench] WARN: benchmark '{label}' ausente; ignorando limiar")
        continue
    worst = max(candidates.values())
    print(f"[microbench] {label} mediana={worst:.4f} ms (limite {limit:.2f} ms)")
    if worst > limit:
        failures.append((label, worst, limit))

if failures:
    for label, value, limit in failures:
        print(f"[microbench] FAIL: {label} excedeu {value:.4f} ms (limite {limit:.2f} ms)")
    sys.exit(1)

print("[microbench] Todos os limiares atendidos")
PY
