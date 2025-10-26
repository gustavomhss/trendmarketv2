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

RUN_PROFILE_RAW="${RUN_PROFILE:-fast}"
RUN_PROFILE="$(printf '%s' "$RUN_PROFILE_RAW" | tr '[:upper:]' '[:lower:]')"
if [[ "$RUN_PROFILE" != "fast" && "$RUN_PROFILE" != "full" ]]; then
  echo "[orr_all] invalid RUN_PROFILE: $RUN_PROFILE_RAW (use fast or full)" >&2
  exit 1
fi

PUBLISH_MODE="${PUBLISH_MODE:-dry-run}"
TARGET_OUT="$ROOT/out/obs_gatecheck"
TARGET_EVI=""
SEED_DIR="$ROOT/seeds"

while [[ $# -gt 0 ]]; do
  case "$1" in
    --seed-dir)
      shift
      SEED_DIR="${1:-$SEED_DIR}"
      shift || true
      ;;
    --out)
      shift
      TARGET_OUT="${1:-$TARGET_OUT}"
      shift || true
      ;;
    --evidence)
      shift
      TARGET_EVI="${1:-$TARGET_EVI}"
      shift || true
      ;;
    --real)
      PUBLISH_MODE="real"
      shift
      ;;
    --dry-run)
      PUBLISH_MODE="dry-run"
      shift
      ;;
    *)
      echo "[orr_all] unknown argument: $1" >&2
      exit 1
      ;;
  esac
done

PUBLISH_MODE="$(printf '%s' "$PUBLISH_MODE" | tr '[:upper:]' '[:lower:]')"
if [[ "$PUBLISH_MODE" != "dry-run" && "$PUBLISH_MODE" != "real" ]]; then
  echo "[orr_all] invalid PUBLISH_MODE: $PUBLISH_MODE (use dry-run or real)" >&2
  exit 1
fi

if [[ -n "$TARGET_EVI" ]]; then
  mkdir -p "$TARGET_EVI"
  TARGET_EVI="$(cd "$TARGET_EVI" && pwd)"
fi

mkdir -p "$TARGET_OUT"
TARGET_OUT="$(cd "$TARGET_OUT" && pwd)"
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

if [[ -n "$TARGET_EVI" ]]; then
  if [[ "$TARGET_EVI" == "$TARGET_OUT"/* ]]; then
    OUT="$TARGET_OUT"
    EVI="$TARGET_EVI"
  elif [[ "$TARGET_OUT" == "$ROOT/out/obs_gatecheck" ]]; then
    OUT="$(cd "$(dirname "$TARGET_EVI")" && pwd)"
    mkdir -p "$OUT"
    EVI="$TARGET_EVI"
  else
    echo "[orr_all] evidence directory ($TARGET_EVI) must reside under $TARGET_OUT" >&2
    exit 1
  fi
else
  OUT="$TARGET_OUT"
  mkdir -p "$OUT"
  EVI="$OUT/evidence"
  mkdir -p "$EVI"
  EVI="$(cd "$EVI" && pwd)"
fi

LOG="$OUT/logs"
mkdir -p "$LOG"
LOG="$(cd "$LOG" && pwd)"

export OUT EVI LOG RUN_PROFILE PUBLISH_MODE
export PROFILE="$RUN_PROFILE"
export EVID="$EVI"

ORR_LOG="$LOG/orr_all.txt"
: > "$ORR_LOG"

timestamp() {
  date -u +"[%H:%M:%S]"
}

log_step() {
  local label="$1"
  local script="$2"
  printf '%s → %s (%s)\n' "$(timestamp)" "$label" "$script" | tee -a "$ORR_LOG"
}

log_skip() {
  local label="$1"
  local script="$2"
  printf '%s ↷ %s (%s) — skipped (profile=%s)\n' "$(timestamp)" "$label" "$script" "$RUN_PROFILE" | tee -a "$ORR_LOG"
}

log_fail() {
  local label="$1"
  local status="$2"
  printf '%s ✖ %s failed (exit=%s)\n' "$(timestamp)" "$label" "$status" | tee -a "$ORR_LOG"
}

should_skip_stage() {
  local label="$1"
  if [[ "$RUN_PROFILE" == "full" ]]; then
    return 1
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
  case "$label" in
    T11_chaos|T12_baseline)
      return 0
      ;;
    *)
      return 1
      ;;
  esac
}

run_stage() {
  local label="$1"
  local log_name="$2"
  local script="$3"
  shift 3
  local log_file="$LOG/${log_name}.txt"

  if should_skip_stage "$label"; then
    log_skip "$label" "$script"
    printf 'SKIPPED (profile=%s)\n' "$RUN_PROFILE" > "$log_file"
    return 0
  fi

  log_step "$label" "$script"
  set +e
  "$@" 2>&1 | tee "$log_file"
  local status=${PIPESTATUS[0]}
  set -e
  if [[ $status -ne 0 ]]; then
    log_fail "$label" "$status"
    exit $status
  fi
}

archive_bundle() {
  local log_file="$LOG/bundle.txt"
  log_step "BUNDLE" "bundle.zip"
  set +e
  {
    rm -f "$OUT/bundle.zip"
    if command -v zip >/dev/null 2>&1; then
      (cd "$OUT" && zip -qr bundle.zip evidence logs)
    else
      python3 - <<'PY'
import os
import zipfile

out = os.environ["OUT"]
evidence = os.environ["EVI"]
logs = os.environ["LOG"]
bundle_path = os.path.join(out, "bundle.zip")
with zipfile.ZipFile(bundle_path, "w", zipfile.ZIP_DEFLATED) as zf:
    for folder in (evidence, logs):
        if not os.path.exists(folder):
            continue
        for root, _, files in os.walk(folder):
            for name in files:
                full = os.path.join(root, name)
                rel = os.path.relpath(full, out)
                zf.write(full, rel)
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
    fi
    if [[ ! -f "$OUT/bundle.zip" ]]; then
      echo "bundle.zip missing" >&2
      exit 1
    fi
    local bundle_sha
    if command -v sha256sum >/dev/null 2>&1; then
      bundle_sha="$(sha256sum "$OUT/bundle.zip" | awk '{print $1}')"
    else
      bundle_sha="$(shasum -a 256 "$OUT/bundle.zip" | awk '{print $1}')"
    fi
    printf '%s\n' "$bundle_sha" > "$OUT/bundle.sha256.txt"
    printf '%s\n' "$bundle_sha" > "$EVI/bundle.sha256.txt"
    echo "bundle_sha256=$bundle_sha"
  } 2>&1 | tee "$log_file"
  local status=${PIPESTATUS[0]}
  set -e
  if [[ $status -ne 0 ]]; then
    log_fail "BUNDLE" "$status"
    exit $status
  fi
}

printf '%s run profile=%s publish_mode=%s\n' "$(timestamp)" "$RUN_PROFILE" "$PUBLISH_MODE" | tee -a "$ORR_LOG"

echo "📂 Evidence root: $OUT"
echo "📁 Evidence dir: $EVI"
echo "🗂  Logs dir: $LOG"
echo "⚙️  Run profile: $RUN_PROFILE"
echo "🚦 Publish mode: $PUBLISH_MODE"
echo "🌱 Seed dir: $SEED_DIR"

cat > "$EVI/env_dump.txt" <<EOF2
RunProfile: $RUN_PROFILE
PublishMode: $PUBLISH_MODE
SeedDir: $SEED_DIR
GeneratedAt: $(date -u +"%Y-%m-%dT%H:%M:%SZ")
OutDir: $OUT
EvidenceDir: $EVI
LogsDir: $LOG
EOF2

run_stage "T1_scan" "t1_scan" "scripts/orr_env_probe.sh" bash "$ROOT/scripts/orr_env_probe.sh"
run_stage "T2_metrics" "t2_metrics" "scripts/orr_t2_parse_unit.py" python3 "$ROOT/scripts/orr_t2_parse_unit.py"
run_stage "T3_tracelog" "t3_tracelog" "scripts/orr_t3_props_run.sh" bash "$ROOT/scripts/orr_t3_props_run.sh"
run_stage "T4_queries" "t4_queries" "scripts/orr_t4_goldens_run.sh" bash "$ROOT/scripts/orr_t4_goldens_run.sh"
run_stage "T5_overhead" "t5_overhead" "scripts/orr_t5_bench_run.sh" bash "$ROOT/scripts/orr_t5_bench_run.sh"
run_stage "T5_collect" "t5_collect" "scripts/orr_t5_collect_criterion.py" python3 "$ROOT/scripts/orr_t5_collect_criterion.py"
run_stage "T6_watchers" "t6_watchers" "scripts/orr_t6_metrics_run.sh" bash "$ROOT/scripts/orr_t6_metrics_run.sh"
run_stage "T7_ci_prep" "t7_ci_prep" "scripts/orr_t7_ci_prep.sh" bash "$ROOT/scripts/orr_t7_ci_prep.sh"
run_stage "T7_ci_collect" "t7_ci_collect" "scripts/orr_t7_collect_ci.sh" bash "$ROOT/scripts/orr_t7_collect_ci.sh"
run_stage "T8_policy" "t8_policy" "scripts/policy_engine.sh" bash "$ROOT/scripts/policy_engine.sh" --emit-policy-hash --out "$EVI"
run_stage "T9_pii" "t9_pii" "scripts/obs_sec_redteam.sh" bash "$ROOT/scripts/obs_sec_redteam.sh"
run_stage "T10_probe" "t10_probe" "scripts/obs_probe_synthetic.sh" bash "$ROOT/scripts/obs_probe_synthetic.sh"
run_stage "T11_chaos" "t11_chaos" "scripts/obs_chaos.sh" bash "$ROOT/scripts/obs_chaos.sh"
run_stage "T12_costs" "t12_costs" "scripts/obs_cardinality_costs.py" python3 "$ROOT/scripts/obs_cardinality_costs.py"
run_stage "T12_sbom" "t12_sbom" "scripts/obs_sbom.sh" bash "$ROOT/scripts/obs_sbom.sh"
run_stage "T12_baseline" "t12_baseline" "scripts/obs_baseline_perf.sh" bash "$ROOT/scripts/obs_baseline_perf.sh"
run_stage "T12_traces" "t12_traces" "scripts/obs_trace_golden.sh" bash "$ROOT/scripts/obs_trace_golden.sh"

archive_bundle

run_stage "GOV_signatures" "gov_signatures" "scripts/provenance/verify_signatures.sh" bash "$ROOT/scripts/provenance/verify_signatures.sh" --evidence "$EVI"
PUBLISH_ARGS=(--evidence "$EVI")
if [[ "$PUBLISH_MODE" == "real" ]]; then
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
run_stage "GOV_publish" "gov_publish" "scripts/provenance/publish_root.sh" bash "$ROOT/scripts/provenance/publish_root.sh" "${PUBLISH_ARGS[@]}"
run_stage "T8_spec_check" "t8_spec_check" "scripts/spec_check.sh" bash "$ROOT/scripts/spec_check.sh" --out "$EVI"

printf '\n[orr_all] Evidence summary:\n'
for path in \
  "$EVI/spec_check.txt" \
  "$EVI/policy_hash.txt" \
  "$EVI/bundle.sha256.txt" \
  "$EVI/provenance_onchain.json" \
  "$EVI/signatures.json" \
  "$OUT/bundle.zip"; do
  if [[ -f "$path" ]]; then
    if size=$(stat -c '%s' "$path" 2>/dev/null); then
      :
    else
      size=$(stat -f '%z' "$path" 2>/dev/null || echo '?')
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

printf 'ACCEPTANCE_OK\n' | tee -a "$ORR_LOG"
printf 'GATECHECK_OK\n' | tee -a "$ORR_LOG"

run_stage "SUMMARY" "summary" "scripts/orr_t9_summary.sh" bash "$ROOT/scripts/orr_t9_summary.sh"
echo 'ACCEPTANCE_OK'
echo 'GATECHECK_OK'

missing=()
[[ -s "$EVI/policy_hash.txt" ]] || missing+=(policy_hash.txt)
[[ -s "$EVI/spec_check.txt" ]] || missing+=(spec_check.txt)
if [[ ${#missing[@]} -gt 0 ]]; then
  echo "❌ Missing in evidence: ${missing[*]}" >&2
  exit 1
fi
if grep -q "RESULT=FAIL" "$EVI/spec_check.txt" 2>/dev/null; then
  echo "❌ spec_check FAIL — see $EVI/spec_check.txt" >&2
  exit 1
fi
echo "✅ Evidence self-check PASS"
