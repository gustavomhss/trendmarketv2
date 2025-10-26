#!/usr/bin/env bash
set -euo pipefail
IFS=$'\n\t'
export LC_ALL=C
export TZ=UTC

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
OUT_DIR="$ROOT/../out/orr_gatecheck/evidence"
SEED_FILE="$ROOT/data/cdc/seeds/engine/burnrate_seed.json"

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
      echo "[burnrate] argumento desconhecido: $1" >&2
      exit 1
      ;;
  esac
done

if [[ ! -f "$SEED_FILE" ]]; then
  echo "[burnrate] seed não encontrada: $SEED_FILE" >&2
  exit 1
fi

readarray -t DATA < <(python - "$SEED_FILE" <<'PY'
import json, sys
path = sys.argv[1]
with open(path, 'r', encoding='utf-8') as fp:
    seed = json.load(fp)
print(seed["timestamp"])
print(seed["window"])
print(seed["burn_rate"])
print(seed["ci95_low"])
print(seed["ci95_high"])
print(seed["budget_threshold"])
PY
)

TS="${DATA[0]}"
WINDOW="${DATA[1]}"
BURN="${DATA[2]}"
CI_LOW="${DATA[3]}"
CI_HIGH="${DATA[4]}"
BUDGET="${DATA[5]}"

mkdir -p "$OUT_DIR/analysis" "$OUT_DIR/burnrate"

cat > "$OUT_DIR/analysis/burnrate_report.csv" <<CSV
timestamp,window,burn_rate,ci95_low,ci95_high,budget_threshold
${TS},${WINDOW},${BURN},${CI_LOW},${CI_HIGH},${BUDGET}
CSV

cat > "$OUT_DIR/burnrate/forecast_window.json" <<JSON
{
  "timestamp": "${TS}",
  "window": "${WINDOW}",
  "burn_rate": ${BURN},
  "ci95": {
    "low": ${CI_LOW},
    "high": ${CI_HIGH}
  },
  "budget_threshold": ${BUDGET}
}
JSON

if command -v convert >/dev/null 2>&1; then
  convert -size 1000x360 xc:white -gravity center -pointsize 22 \
    -fill black -annotate 0 "Burn-rate ${WINDOW}: ${BURN}x (CI95% ${CI_LOW}-${CI_HIGH})" \
    "$OUT_DIR/analysis/burnrate_chart.png"
else
  echo "convert ausente; gráfico substituído por descrição textual" > "$OUT_DIR/analysis/burnrate_chart.txt"
fi

echo "[burnrate] relatório gerado em ${OUT_DIR}"
