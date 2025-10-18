#!/usr/bin/env bash
set -euo pipefail
IFS=$'\n\t'
export LC_ALL=C
export TZ=UTC

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$SCRIPT_DIR/.."
EVID_DIR="$ROOT/../out/orr_gatecheck/evidence"
SEED_DIR="$ROOT/seeds"
HOOK_MODE="fast"

while [[ $# -gt 0 ]]; do
  case "$1" in
    --seed-dir)
      SEED_DIR="$(cd "$2" && pwd)"
      shift 2
      ;;
    --real)
      HOOK_MODE="real"
      shift
      ;;
    *)
      echo "[orr_all] argumento desconhecido: $1" >&2
      exit 1
      ;;
  esac
done

mkdir -p "$EVID_DIR" "$EVID_DIR/dashboards" "$EVID_DIR/analysis" \
  "$EVID_DIR/rum" "$EVID_DIR/obs_self" "$EVID_DIR/burnrate" "$EVID_DIR/hooks"

printf '[orr_all] etapa 1/8 — análises\n'
bash "$ROOT/scripts/analysis/run_all.sh" --out "$EVID_DIR" --seed-dir "$SEED_DIR"
if command -v convert >/dev/null 2>&1; then
  convert -size 1754x1240 xc:white -gravity center -pointsize 36 -fill black \
    -annotate 0 "MBP Sprint 2 — Evidence Poster" "$EVID_DIR/dashboards/poster_a4.png"
else
  echo "Poster indisponível (convert ausente)" > "$EVID_DIR/dashboards/poster_a4.txt"
fi

printf '[orr_all] etapa 2/8 — hooks sintéticos (%s)\n' "$HOOK_MODE"
HOOKS=(
  hook_invariant_breach
  hook_latency_budget
  hook_resolution_sla
  hook_cdc_lag
  hook_schema_drift
  hook_api_contract_break
  hook_web_cwv_regression
)
for hook in "${HOOKS[@]}"; do
  HOOK_SCRIPT="$ROOT/scripts/hooks/${hook}.sh"
  OUT_FILE="$EVID_DIR/hooks/${hook}.json"
  if [[ "$HOOK_MODE" == "real" ]]; then
    bash "$HOOK_SCRIPT" --real --out "$OUT_FILE"
  else
    bash "$HOOK_SCRIPT" --out "$OUT_FILE"
  fi
done

printf '[orr_all] etapa 3/8 — policy engine\n'
bash "$ROOT/scripts/policy_engine.sh" --emit-policy-hash --out "$EVID_DIR" --seed-file "$SEED_DIR/engine/policy_metrics.json"
python - "$SEED_DIR/engine/policy_metrics.json" "$EVID_DIR/env_dump.txt" <<'PY'
import json, sys
with open(sys.argv[1], 'r', encoding='utf-8') as fp:
    metrics = json.load(fp)
with open(sys.argv[2], 'w', encoding='utf-8') as fp:
    fp.write(f"HistogramSchemaVersion: {metrics['histogram_schema_version']}\n")
    fp.write(f"ResilienceIndexFast: {metrics['resilience_index_fast']}\n")
    fp.write(f"ResilienceIndexNightly: {metrics['resilience_index_nightly']}\n")
PY

printf '[orr_all] etapa 4/8 — simulações determinísticas\n'
bash "$ROOT/scripts/sim_run.sh" --mode fast
bash "$ROOT/scripts/sim_run.sh" --mode nightly
bash "$ROOT/scripts/chaos_weekly.sh" --evidence "$EVID_DIR"

printf '[orr_all] etapa 5/8 — geração do bundle SHA\n'
BUNDLE_FILE="$EVID_DIR/bundle.sha256.txt"
BUNDLE_SHA=$(git -C "$ROOT" ls-files -z | xargs -0 sha256sum | LC_ALL=C sort -k2 | sha256sum | awk '{print $1}')
printf '%s\n' "$BUNDLE_SHA" > "$BUNDLE_FILE"

printf '[orr_all] etapa 6/8 — governança (assinaturas + provenance)\n'
bash "$ROOT/scripts/provenance/verify_signatures.sh" --evidence "$EVID_DIR"
bash "$ROOT/scripts/provenance/publish_root.sh" --evidence "$EVID_DIR" --dry-run

printf '[orr_all] etapa 7/8 — spec check\n'
bash "$ROOT/scripts/spec_check.sh" --out "$EVID_DIR"

printf '[orr_all] etapa 8/8 — manifesto de hashes\n'
bash "$ROOT/scripts/analysis/hash_manifest.sh" --evidence "$EVID_DIR"

printf '\n[orr_all] Sumário de evidências relevantes:\n'
for path in \
  "$EVID_DIR/spec_check.txt" \
  "$EVID_DIR/policy_hash.txt" \
  "$EVID_DIR/bundle.sha256.txt" \
  "$EVID_DIR/provenance_onchain.json" \
  "$EVID_DIR/signatures.json"; do
  if [[ -f "$path" ]]; then
    size=$(stat -c '%s' "$path")
    printf '  - %s (%s bytes)\n' "$path" "$size"
  fi
done

printf 'ACCEPTANCE_OK\n'
printf 'GATECHECK_OK\n'
