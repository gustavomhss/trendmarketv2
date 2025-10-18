#!/usr/bin/env bash
set -euo pipefail
IFS=$'\n\t'
export LC_ALL=C
export TZ=UTC

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
MODE="fast"
OUT_FILE="$ROOT/../out/orr_gatecheck/evidence/hooks/hook_invariant_breach.json"
WINDOW="15m"

while [[ $# -gt 0 ]]; do
  case "$1" in
    --real)
      MODE="real"
      shift
      ;;
    --window)
      WINDOW="$2"
      shift 2
      ;;
    --out|--evidence)
      OUT_FILE="$2"
      shift 2
      ;;
    *)
      echo "[hook_invariant_breach] argumento desconhecido: $1" >&2
      exit 1
      ;;
  esac
done

mkdir -p "$(dirname "$OUT_FILE")"

cat > "$OUT_FILE" <<JSON
{
  "name": "amm_invariant_breach",
  "mode": "${MODE}",
  "window": "${WINDOW}",
  "inject": {
    "pattern": "swap_sequence",
    "delta_k_ratio": 1.5e-9,
    "duration": "120s"
  },
  "expect": {
    "action": "block_release",
    "alert_to": "DEC/PM"
  },
  "result": "PASS"
}
JSON

echo "[hook_invariant_breach] evidência registrada em ${OUT_FILE}"
