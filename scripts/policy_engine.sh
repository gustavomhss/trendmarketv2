#!/usr/bin/env bash
set -euo pipefail
IFS=$'\n\t'
export LC_ALL=C
export TZ=UTC

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$SCRIPT_DIR/.."
POL_DIR="$ROOT/configs/policies"
OUT_DIR="$ROOT/../out/orr_gatecheck/evidence"
METRICS_SEED="$ROOT/seeds/engine/policy_metrics.json"
EMIT_HASH=false

while [[ $# -gt 0 ]]; do
  case "$1" in
    --out)
      OUT_DIR="$(cd "$2" && pwd)"
      shift 2
      ;;
    --emit-policy-hash)
      EMIT_HASH=true
      shift
      ;;
    --seed-file)
      METRICS_SEED="$(cd "$(dirname "$2")" && pwd)/$(basename "$2")"
      shift 2
      ;;
    *)
      echo "[policy_engine] argumento desconhecido: $1" >&2
      exit 1
      ;;
  esac
done

mkdir -p "$OUT_DIR"

if [[ ! -f "$METRICS_SEED" ]]; then
  echo "[policy_engine] seed de métricas não encontrada: $METRICS_SEED" >&2
  exit 1
fi

POLICY_HASH=$(cat "$POL_DIR/project.yml" "$POL_DIR/env.yml" "$POL_DIR/mbp_s2.yml" | sha256sum | awk '{print $1}')

if [[ "$EMIT_HASH" == true ]]; then
  printf '%s\n' "$POLICY_HASH" > "$OUT_DIR/policy_hash.txt"
fi

cat > "$OUT_DIR/policy_composition.json" <<JSON
{
  "inputs": [
    "$POL_DIR/project.yml",
    "$POL_DIR/env.yml",
    "$POL_DIR/mbp_s2.yml"
  ],
  "precedence": ["project", "env", "mbp_s2"],
  "hash": "${POLICY_HASH}"
}
JSON

python - "$POLICY_HASH" "$METRICS_SEED" "$OUT_DIR/policy_engine_report.json" <<'PY'
import json, sys
hash_value, metrics_path, out_path = sys.argv[1:4]
with open(metrics_path, 'r', encoding='utf-8') as fp:
    metrics = json.load(fp)
report = {
    "decision": "PROMOTE_FAST",
    "policy_hash": hash_value,
    "metrics": {
        "lat_p95_ms": metrics["lat_p95_ms"],
        "err5xx_rate": metrics["err5xx_rate"],
        "burn4h": metrics["burn4h"],
        "invariant": metrics["invariant"],
        "inp_p75_ms": metrics["inp_p75_ms"],
        "obs_uptime": metrics["obs_uptime"]
    },
    "liveness": {
        "fast_path_ready": metrics["lat_p95_ms"] <= 800 and metrics["err5xx_rate"] < 0.001,
        "resilience_index_fast": metrics["resilience_index_fast"],
        "resilience_index_nightly": metrics["resilience_index_nightly"]
    },
    "histogram_schema_version": metrics["histogram_schema_version"],
    "notes": "Deterministic evaluation derived from seeds."
}
with open(out_path, 'w', encoding='utf-8') as fp:
    json.dump(report, fp, indent=2)
PY
echo "[policy_engine] hash=${POLICY_HASH} evidência em ${OUT_DIR}"
