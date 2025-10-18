#!/usr/bin/env bash
set -euo pipefail
IFS=$'\n\t'; export LC_ALL=C; export TZ=UTC

# ── Paths base ───────────────────────────────────────────────────────────────────
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"                  # repo root
DEFAULT_EVID="$ROOT/out/orr_gatecheck/evidence"       # canônico dentro do repo

# Evidence precedence: Ambiente (EVID) → CLI (--out/--evidence) → Default
EVID="${EVID:-$DEFAULT_EVID}"

# Seeds (default)
SEED_DIR="$ROOT/seeds"

# Hooks: modo padrão "fast" (sintético, sem side-effects)
HOOK_MODE="fast"

# Publicação: default "dry-run" (pode ser sobrescrito por env PUBLISH_MODE=real)
MODE_PUBLISH="${PUBLISH_MODE:-dry-run}"

# ── Args ────────────────────────────────────────────────────────────────────────
while [[ $# -gt 0 ]]; do
  case "$1" in
    --seed-dir)
      shift
      SEED_DIR="$(cd "${1:-$SEED_DIR}" && pwd)"
      shift || true
      ;;
    --out|--evidence)
      shift
      EVID="$(cd "${1:-$EVID}" && pwd)"
      shift || true
      ;;
    --real)
      HOOK_MODE="real"
      MODE_PUBLISH="real"
      shift
      ;;
    *)
      echo "[orr_all] argumento desconhecido: $1" >&2
      exit 1
      ;;
  esac
done
export EVID

# ── Dirs de evidence ────────────────────────────────────────────────────────────
mkdir -p "$EVID" \
         "$EVID/dashboards" "$EVID/analysis" "$EVID/rum" \
         "$EVID/obs_self" "$EVID/burnrate" "$EVID/hooks"

echo "📁 Using EVID: $EVID"
echo "🚦 Publish mode: $MODE_PUBLISH"

# ── Etapa 1/8: análises ─────────────────────────────────────────────────────────
printf '[orr_all] etapa 1/8 — análises\n'
bash "$ROOT/scripts/analysis/run_all.sh" --out "$EVID" --seed-dir "$SEED_DIR"

# Poster (best-effort)
if command -v convert >/dev/null 2>&1; then
  convert -size 1754x1240 xc:white -gravity center -pointsize 36 -fill black \
    -annotate 0 "MBP Sprint 2 — Evidence Poster" "$EVID/dashboards/poster_a4.png"
else
  echo "Poster indisponível (convert ausente)" > "$EVID/dashboards/poster_a4.txt"
fi

# ── Etapa 2/8: hooks A110 (fast/real) ──────────────────────────────────────────
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
  OUT_FILE="$EVID/hooks/${hook}.json"
  if [[ "$HOOK_MODE" == "real" ]]; then
    bash "$HOOK_SCRIPT" --real --out "$OUT_FILE"
  else
    bash "$HOOK_SCRIPT" --out "$OUT_FILE"
  fi
done

# ── Etapa 3/8: policy engine + env dump ────────────────────────────────────────
printf '[orr_all] etapa 3/8 — policy engine\n'
bash "$ROOT/scripts/policy_engine.sh" --emit-policy-hash --out "$EVID" --seed-file "$SEED_DIR/engine/policy_metrics.json"
python - "$SEED_DIR/engine/policy_metrics.json" "$EVID/env_dump.txt" <<'PY'
import json, sys
with open(sys.argv[1], 'r', encoding='utf-8') as fp:
    metrics = json.load(fp)
with open(sys.argv[2], 'w', encoding='utf-8') as fp:
    fp.write(f"HistogramSchemaVersion: {metrics['histogram_schema_version']}\n")
    fp.write(f"ResilienceIndexFast: {metrics['resilience_index_fast']}\n")
    fp.write(f"ResilienceIndexNightly: {metrics['resilience_index_nightly']}\n")
PY

# ── Etapa 4/8: simulações determinísticas ──────────────────────────────────────
printf '[orr_all] etapa 4/8 — simulações determinísticas\n'
bash "$ROOT/scripts/sim_run.sh" --mode fast
bash "$ROOT/scripts/sim_run.sh" --mode nightly
bash "$ROOT/scripts/chaos_weekly.sh" --evidence "$EVID"

# ── Etapa 5/8: bundle SHA do repo ──────────────────────────────────────────────
printf '[orr_all] etapa 5/8 — geração do bundle SHA\n'
BUNDLE_FILE="$EVID/bundle.sha256.txt"
BUNDLE_SHA=$(git -C "$ROOT" ls-files -z | xargs -0 sha256sum | LC_ALL=C sort -k2 | sha256sum | awk '{print $1}')
printf '%s\n' "$BUNDLE_SHA" > "$BUNDLE_FILE"

# ── Etapa 6/8: governança (assinaturas + provenance) ───────────────────────────
printf '[orr_all] etapa 6/8 — governança (assinaturas + provenance)\n'
bash "$ROOT/scripts/provenance/verify_signatures.sh" --evidence "$EVID"
PUBLISH_ARGS=(--evidence "$EVID")
if [[ "$MODE_PUBLISH" == "real" ]]; then
  PUBLISH_ARGS+=(--real)
else
  PUBLISH_ARGS+=(--dry-run)
fi
bash "$ROOT/scripts/provenance/publish_root.sh" "${PUBLISH_ARGS[@]}"

# ── Etapa 7/8: spec check ──────────────────────────────────────────────────────
printf '[orr_all] etapa 7/8 — spec check\n'
bash "$ROOT/scripts/spec_check.sh" --out "$EVID"

# ── Etapa 8/8: manifesto de hashes ─────────────────────────────────────────────
printf '[orr_all] etapa 8/8 — manifesto de hashes\n'
bash "$ROOT/scripts/analysis/hash_manifest.sh" --evidence "$EVID"

# ── Sumário de arquivos chave ──────────────────────────────────────────────────
printf '\n[orr_all] Sumário de evidências relevantes:\n'
for path in \
  "$EVID/spec_check.txt" \
  "$EVID/policy_hash.txt" \
  "$EVID/bundle.sha256.txt" \
  "$EVID/provenance_onchain.json" \
  "$EVID/signatures.json"; do
  if [[ -f "$path" ]]; then
    size=$(stat -c '%s' "$path")
    printf '  - %s (%s bytes)\n' "$path" "$size"
  fi
done

printf 'ACCEPTANCE_OK\n'
printf 'GATECHECK_OK\n'

# ── Self-check (GO/NO-GO) ──────────────────────────────────────────────────────
missing=()
[[ -s "$EVID/policy_hash.txt" ]] || missing+=(policy_hash.txt)
[[ -s "$EVID/spec_check.txt" ]] || missing+=(spec_check.txt)
if [[ ${#missing[@]} -gt 0 ]]; then
  echo "❌ Missing in evidence: ${missing[*]}" >&2
  exit 1
fi
if grep -q "RESULT=FAIL" "$EVID/spec_check.txt" 2>/dev/null; then
  echo "❌ spec_check FAIL — see $EVID/spec_check.txt" >&2
  exit 1
fi
echo "✅ Evidence self-check PASS"
