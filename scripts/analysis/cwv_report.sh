#!/usr/bin/env bash
set -euo pipefail
IFS=$'\n\t'
export LC_ALL=C
export TZ=UTC

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
OUT_DIR="$ROOT/../out/orr_gatecheck/evidence"
SEED_FILE="$ROOT/seeds/rum/cwv_seed.json"

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
      echo "[cwv] argumento desconhecido: $1" >&2
      exit 1
      ;;
  esac
done

if [[ ! -f "$SEED_FILE" ]]; then
  echo "[cwv] seed não encontrada: $SEED_FILE" >&2
  exit 1
fi

CSV_BODY=$(python - "$SEED_FILE" <<'PY'
import json, sys
path = sys.argv[1]
with open(path, 'r', encoding='utf-8') as fp:
    seed = json.load(fp)
rows = []
for route in seed["routes"]:
    rows.append(
        f"{route['route']},{route['metric']},{route['baseline']},{route['current']},{route['delta_pct']},{route['p_value']},{route['ci95_low']},{route['ci95_high']}"
    )
print("\n".join(rows))
PY
)

MEETS_RULE=$(python - "$SEED_FILE" <<'PY'
import json, sys
with open(sys.argv[1], 'r', encoding='utf-8') as fp:
    seed = json.load(fp)
print(str(seed.get('meets_ci_rule', False)).lower())
PY
)

mkdir -p "$OUT_DIR/analysis" "$OUT_DIR/rum"

cat > "$OUT_DIR/analysis/cwv_report.csv" <<CSV
route,metric,baseline,current,delta_pct,p_value,ci95_low,ci95_high
${CSV_BODY}
CSV

cp "$SEED_FILE" "$OUT_DIR/rum/diff_report.json"

python - "$SEED_FILE" "$OUT_DIR/rum/confidence_intervals.csv" <<'PY'
import csv, json, sys
seed_path, out_path = sys.argv[1], sys.argv[2]
with open(seed_path, 'r', encoding='utf-8') as fp:
    seed = json.load(fp)
with open(out_path, 'w', encoding='utf-8', newline='') as csvfile:
    writer = csv.writer(csvfile)
    writer.writerow(["route", "ci95_low", "ci95_high"])
    for route in seed["routes"]:
        writer.writerow([route["route"], route["ci95_low"], route["ci95_high"]])
PY

cat > "$OUT_DIR/rum/summary.json" <<JSON
{
  "meets_ci_rule": ${MEETS_RULE},
  "seed": "$(python - "$SEED_FILE" <<'PY'
import json, sys
with open(sys.argv[1], 'r', encoding='utf-8') as fp:
    seed = json.load(fp)
print(seed.get('seed', ''))
PY
)"
}
JSON

if command -v convert >/dev/null 2>&1; then
  convert -size 1000x360 xc:white -gravity center -pointsize 22 \
    -fill black -annotate 0 "CWV Δ<=10% e p<=0.1? ${MEETS_RULE^^}" \
    "$OUT_DIR/analysis/cwv_chart.png"
else
  echo "convert ausente; resumo CWV registrado em texto" > "$OUT_DIR/analysis/cwv_chart.txt"
fi

echo "[cwv] relatório gerado em ${OUT_DIR}"
