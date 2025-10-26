#!/usr/bin/env bash
set -euo pipefail
IFS=$'\n\t'
export LC_ALL=C
export TZ=UTC

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
OUT_DIR="$ROOT/../out/orr_gatecheck/evidence"
SEED_FILE="$ROOT/data/cdc/seeds/load/cardinality_seed.json"

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
      echo "[cardinality] argumento desconhecido: $1" >&2
      exit 1
      ;;
  esac
done

if [[ ! -f "$SEED_FILE" ]]; then
  echo "[cardinality] seed não encontrada: $SEED_FILE" >&2
  exit 1
fi

readarray -t ROWS < <(python - "$SEED_FILE" <<'PY'
import json, sys
seed_path = sys.argv[1]
with open(seed_path, 'r', encoding='utf-8') as fp:
    seed = json.load(fp)
series = seed["series_active"]
budget_global = seed["budget_global"]
total = sum(series.values())
status = "OK" if total <= budget_global else "BREACH"
print(seed["sampled_at"])
print(total)
print(budget_global)
print(status)
for domain, value in series.items():
    limit = {
        "DEC": 2000,
        "MBP": 3000,
        "FE": 2000,
        "DATA": 2000,
        "INT": 1000,
        "SEC": 1000
    }.get(domain, budget_global)
    domain_status = "OK" if value <= limit else "BREACH"
    over = max(0, value - limit)
    print(f"{domain},{value},{limit},{domain_status},{over}")
PY
)

SAMPLED_AT="${ROWS[0]}"
TOTAL="${ROWS[1]}"
GLOBAL_LIMIT="${ROWS[2]}"
STATUS="${ROWS[3]}"
DOMAIN_ROWS=()
for ((i=4; i<${#ROWS[@]}; i++)); do
  DOMAIN_ROWS+=("${ROWS[$i]}")
done

mkdir -p "$OUT_DIR/analysis"

{
  echo "series_active=${TOTAL}, budget_global=${GLOBAL_LIMIT}, status=${STATUS}"
  echo "sampled_at=${SAMPLED_AT}"
} > "$OUT_DIR/cardinality.txt"

{
  echo "domain,active,limit,status,excess"
  for row in "${DOMAIN_ROWS[@]}"; do
    echo "$row"
  done
} > "$OUT_DIR/analysis/cardinality_budget.csv"

if command -v convert >/dev/null 2>&1; then
  LABEL="Cardinality ${TOTAL}/${GLOBAL_LIMIT} (${STATUS})"
  convert -size 1000x360 xc:white -gravity center -pointsize 22 -fill black \
    -annotate 0 "$LABEL" "$OUT_DIR/analysis/cardinality_chart.png"
else
  echo "convert ausente; gráfico de cardinalidade registrado em texto" > "$OUT_DIR/analysis/cardinality_chart.txt"
fi

echo "[cardinality] relatório gerado em ${OUT_DIR}"
