#!/usr/bin/env bash
set -euo pipefail
IFS=$'\n\t'; export LC_ALL=C; export TZ=UTC

timestamp() {
  date -u +"%Y-%m-%dT%H:%M:%SZ"
}

RUN_PROFILE="${RUN_PROFILE:-fast}"
case "$RUN_PROFILE" in
  fast|full) ;;
  *)
    echo "[orr_all] RUN_PROFILE inválido: $RUN_PROFILE" >&2
    echo "Use RUN_PROFILE=fast (default) ou RUN_PROFILE=full." >&2
    exit 1
    ;;
esac

# ── Paths base ───────────────────────────────────────────────────────────────────
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"                  # repo root
DEFAULT_OUT="$ROOT/out/obs_gatecheck"
DEFAULT_EVID="$DEFAULT_OUT/evidence"                  # canônico dentro do repo

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
export PROFILE="$RUN_PROFILE"

OUT_DIR="$(cd "$(dirname "$EVID")" && pwd)"
LOG_DIR="$OUT_DIR/logs"
LOG_FILE="$LOG_DIR/orr_all.txt"

# ── Dirs de evidence ────────────────────────────────────────────────────────────
mkdir -p "$EVID" \
         "$EVID/dashboards" "$EVID/analysis" "$EVID/rum" \
         "$EVID/obs_self" "$EVID/burnrate" "$EVID/hooks"
mkdir -p "$LOG_DIR"

: > "$LOG_FILE"
exec > >(tee -a "$LOG_FILE")
exec 2> >(tee -a "$LOG_FILE" >&2)

echo "[$(timestamp)] RUN_PROFILE=$RUN_PROFILE"
echo "[$(timestamp)] 📁 Using EVID: $EVID"
echo "[$(timestamp)] 📓 Logs: $LOG_DIR"
echo "[$(timestamp)] 🚦 Publish mode: $MODE_PUBLISH"

# ── Preflight para perfil full ─────────────────────────────────────────────────
if [[ "$RUN_PROFILE" == "full" ]]; then
  echo "[$(timestamp)] → Preflight cargo (fetch/build/fmt/clippy/test)"
  if command -v cargo >/dev/null 2>&1; then
    (
      cd "$ROOT"
      cargo fetch
      cargo build
      cargo fmt -- --check
      cargo clippy -- -D warnings
      cargo test
    )
  else
    echo "[orr_all] cargo indisponível — pulando etapa full de build/test"
  fi

  echo "[$(timestamp)] → Preflight supply-chain (cargo deny & audit)"
  if command -v cargo >/dev/null 2>&1 && cargo deny --help >/dev/null 2>&1; then
    (cd "$ROOT" && cargo deny check)
  else
    echo "[orr_all] cargo deny indisponível — skip"
  fi
  if command -v cargo >/dev/null 2>&1 && cargo audit --help >/dev/null 2>&1; then
    (cd "$ROOT" && cargo audit)
  else
    echo "[orr_all] cargo audit indisponível — skip"
  fi
fi

# ── Stage: análises ────────────────────────────────────────────────────────────
echo "[$(timestamp)] → Análises determinísticas"
bash "$ROOT/scripts/analysis/run_all.sh" --out "$EVID" --seed-dir "$SEED_DIR"

# Poster (best-effort)
if command -v convert >/dev/null 2>&1; then
  convert -size 1754x1240 xc:white -gravity center -pointsize 36 -fill black \
    -annotate 0 "MBP Sprint 2 — Evidence Poster" "$EVID/dashboards/poster_a4.png"
else
  echo "Poster indisponível (convert ausente)" > "$EVID/dashboards/poster_a4.txt"
fi

# ── Stage: hooks A110 (fast/real) ───────────────────────────────────────────────
echo "[$(timestamp)] → Hooks sintéticos (${HOOK_MODE})"
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

# ── Stage: policy engine + env dump ────────────────────────────────────────────
echo "[$(timestamp)] → Policy engine"
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

# ── Stage: simulações determinísticas ──────────────────────────────────────────
echo "[$(timestamp)] → Simulações determinísticas (fast/nightly + chaos weekly)"
bash "$ROOT/scripts/sim_run.sh" --mode fast
bash "$ROOT/scripts/sim_run.sh" --mode nightly
bash "$ROOT/scripts/chaos_weekly.sh" --evidence "$EVID"

# ── Stage: bundle SHA do repo ──────────────────────────────────────────────────
echo "[$(timestamp)] → Geração do bundle SHA"
BUNDLE_FILE="$EVID/bundle.sha256.txt"
BUNDLE_SHA=$(git -C "$ROOT" ls-files -z | xargs -0 sha256sum | LC_ALL=C sort -k2 | sha256sum | awk '{print $1}')
printf '%s\n' "$BUNDLE_SHA" > "$BUNDLE_FILE"

# ── Stage: governança (assinaturas + provenance) ───────────────────────────────
echo "[$(timestamp)] → Governança (assinaturas + provenance)"
bash "$ROOT/scripts/provenance/verify_signatures.sh" --evidence "$EVID"
PUBLISH_ARGS=(--evidence "$EVID")
if [[ "$MODE_PUBLISH" == "real" ]]; then
  PUBLISH_ARGS+=(--real)
else
  PUBLISH_ARGS+=(--dry-run)
fi
bash "$ROOT/scripts/provenance/publish_root.sh" "${PUBLISH_ARGS[@]}"

# ── Stage: spec check ──────────────────────────────────────────────────────────
echo "[$(timestamp)] → Spec check"
bash "$ROOT/scripts/spec_check.sh" --out "$EVID"

# ── Stage: manifesto de hashes ─────────────────────────────────────────────────
echo "[$(timestamp)] → Manifesto de hashes"
bash "$ROOT/scripts/analysis/hash_manifest.sh" --evidence "$EVID"

# ── Stages extras (RUN_PROFILE=full) ────────────────────────────────────────────
if [[ "$RUN_PROFILE" == "full" ]]; then
  echo "[$(timestamp)] → T9 PII Red Team"
  bash "$ROOT/scripts/obs_sec_redteam.sh" | tee "$LOG_DIR/t9_pii.txt"

  echo "[$(timestamp)] → T10 Synthetic prober"
  bash "$ROOT/scripts/obs_probe_synthetic.sh" | tee "$LOG_DIR/t10_probe.txt"

  echo "[$(timestamp)] → T11 Chaos drills"
  bash "$ROOT/scripts/obs_chaos.sh" | tee "$LOG_DIR/t11_chaos.txt"

  echo "[$(timestamp)] → T12 Costs & cardinality"
  python3 "$ROOT/scripts/obs_cardinality_costs.py" | tee "$LOG_DIR/t12_costs.txt"

  echo "[$(timestamp)] → T12 SBOM"
  bash "$ROOT/scripts/obs_sbom.sh" | tee "$LOG_DIR/t12_sbom.txt"

  echo "[$(timestamp)] → T12 Baseline perf"
  bash "$ROOT/scripts/obs_baseline_perf.sh" | tee "$LOG_DIR/t12_baseline.txt"

  echo "[$(timestamp)] → T12 Golden traces"
  bash "$ROOT/scripts/obs_trace_golden.sh" | tee "$LOG_DIR/t12_traces.txt"
fi

# ── Sumário de arquivos chave ──────────────────────────────────────────────────
echo
echo "[orr_all] Sumário de evidências relevantes:"
for path in \
  "$EVID/spec_check.txt" \
  "$EVID/policy_hash.txt" \
  "$EVID/bundle.sha256.txt" \
  "$EVID/provenance_onchain.json" \
  "$EVID/signatures.json" \
  "$EVID/costs_cardinality.json" \
  "$EVID/sbom.cdx.json" \
  "$EVID/baseline_perf.json" \
  "$EVID/golden_traces.json"; do
  if [[ -f "$path" ]]; then
    if command -v stat >/dev/null 2>&1; then
      size=$(stat -c '%s' "$path" 2>/dev/null || stat -f '%z' "$path" 2>/dev/null || echo "?")
    else
      size="?"
    fi
    printf '  - %s (%s bytes)\n' "$path" "$size"
  fi
done

echo 'ACCEPTANCE_OK'
echo 'GATECHECK_OK'

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
