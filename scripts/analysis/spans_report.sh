#!/usr/bin/env bash
set -euo pipefail
IFS=$'\n\t'
export LC_ALL=C
export TZ=UTC

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
OUT_DIR="$ROOT/../out/orr_gatecheck/evidence"
SEED_FILE="$ROOT/data/cdc/seeds/engine/spans_seed.json"

while [[ $# -gt 0 ]]; do
  case "$1" in
    --out)
      OUT_DIR="$(cd "$2" && pwd)"
      shift 2
      ;;
    --seed-file)
      SEED_FILE="$(cd "$(dirname "$2")" && pwd)/$(basename "$2")"
      shift 2
      ;;
    *)
      echo "[spans] argumento desconhecido: $1" >&2
      exit 1
      ;;
  esac
done

if [[ ! -f "$SEED_FILE" ]]; then
  echo "[spans] seed não encontrada: $SEED_FILE" >&2
  exit 1
fi

readarray -t DATA < <(python - "$SEED_FILE" <<'PY'
import json, sys
path = sys.argv[1]
with open(path, 'r', encoding='utf-8') as fp:
    seed = json.load(fp)
print(seed["timestamp"])
print(seed["span_coverage_pct"])
print(seed["p95_latency_ms"])
PY
)

TS="${DATA[0]}"
COVERAGE="${DATA[1]}"
LAT_P95="${DATA[2]}"

mkdir -p "$OUT_DIR/analysis" "$OUT_DIR/traces"

cat > "$OUT_DIR/analysis/spans_report.csv" <<CSV
timestamp,span_coverage_pct,p95_latency_ms
${TS},${COVERAGE},${LAT_P95}
CSV

echo "${COVERAGE}" > "$OUT_DIR/traces/span_coverage.txt"

if command -v convert >/dev/null 2>&1; then
  convert -size 1000x360 xc:white -gravity center -pointsize 22 \
    -fill black -annotate 0 "Span coverage ${COVERAGE}% | P95 ${LAT_P95}ms" \
    "$OUT_DIR/analysis/spans_chart.png"
else
  echo "convert ausente; resumo spans registrado em texto" > "$OUT_DIR/analysis/spans_chart.txt"
fi

echo "[spans] relatório gerado em ${OUT_DIR}"
