#!/usr/bin/env bash
set -euo pipefail
IFS=$'\n\t'
export LC_ALL=C
export TZ=UTC

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$SCRIPT_DIR/.."
OUT_DIR="$ROOT/../out/sim"
MODE="fast"
REAL_MODE=false
METRICS_SEED="$ROOT/seeds/engine/policy_metrics.json"

while [[ $# -gt 0 ]]; do
  case "$1" in
    --mode)
      MODE="$2"
      shift 2
      ;;
    --real)
      REAL_MODE=true
      shift
      ;;
    --out)
      OUT_DIR="$(cd "$2" && pwd)"
      shift 2
      ;;
    --seed-file)
      METRICS_SEED="$(cd "$(dirname "$2")" && pwd)/$(basename "$2")"
      shift 2
      ;;
    *)
      echo "[sim_run] argumento desconhecido: $1" >&2
      exit 1
      ;;
  esac
done

mkdir -p "$OUT_DIR"

readarray -t DATA < <(python - "$METRICS_SEED" <<'PY'
import json, sys
with open(sys.argv[1], 'r', encoding='utf-8') as fp:
    seed = json.load(fp)
print(seed.get('resilience_index_fast', 0))
print(seed.get('resilience_index_nightly', 0))
PY
)

FAST_INDEX="${DATA[0]}"
NIGHTLY_INDEX="${DATA[1]}"
REAL_FLAG=false
if [[ "$REAL_MODE" == true ]]; then
  REAL_FLAG=true
fi

case "$MODE" in
  fast)
    cat > "$OUT_DIR/report_fast.json" <<JSON
{
  "scenario": "fast",
  "resilience_index": ${FAST_INDEX},
  "real_mode": ${REAL_FLAG}
}
JSON
    ;;
  nightly)
    cat > "$OUT_DIR/report_nightly.json" <<JSON
{
  "scenario": "nightly",
  "resilience_index": ${NIGHTLY_INDEX},
  "real_mode": ${REAL_FLAG}
}
JSON
    ;;
  *)
    echo "[sim_run] modo desconhecido: ${MODE}" >&2
    exit 1
    ;;
esac

echo "[sim_run] relatório ${MODE} gerado em ${OUT_DIR}"
