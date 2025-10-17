#!/usr/bin/env bash
set -euo pipefail

OUT="out/obs_gatecheck"
EVI="$OUT/evidence"
LOG="$OUT/logs"
mkdir -p "$EVI" "$LOG"

log() {
  echo "[$(date -u +%H:%M:%S)] $*" | tee -a "$LOG/orr_all.txt"
}

run() {
  local n="$1"; shift
  local script="$1"; shift || true
  log "→ $n ($script)"
  if [[ "$script" == *.py ]]; then
    python3 "$script" "$@" 2>&1 | tee -a "$LOG/${n}.txt"
  else
    bash "$script" "$@" 2>&1 | tee -a "$LOG/${n}.txt"
  fi
}

run T0_env scripts/orr_env_probe.sh
run T1_run scripts/orr_t1_run.sh
run T2_parse scripts/orr_t2_parse_unit.py
run T3_props scripts/orr_t3_props_run.sh
run T4_goldens scripts/orr_t4_goldens_run.sh
run T5_bench scripts/orr_t5_bench_run.sh
run T5_collect scripts/orr_t5_collect_criterion.py
run T6_metrics scripts/orr_t6_metrics_run.sh
run T7_ci_prep scripts/orr_t7_ci_prep.sh
run T7_collect scripts/orr_t7_collect_ci.sh
run T9_pii scripts/obs_sec_redteam.sh
run T10_probe scripts/obs_probe_synthetic.sh
run T11_chaos scripts/obs_chaos.sh
run T12_costs scripts/obs_cardinality_costs.py
run T12_sbom scripts/obs_sbom.sh
run T12_baseline scripts/obs_baseline_perf.sh
run T12_traces scripts/obs_trace_golden.sh
run T8_bundle scripts/orr_t8_bundle.sh

log "ACCEPTANCE_OK"; echo ACCEPTANCE_OK
log "GATECHECK_OK"; echo GATECHECK_OK

run T9_summary scripts/orr_t9_summary.sh
run T13_release scripts/obs_release_manifest.py
run T14_finalize scripts/obs_release_finalize.py
run T15_notes scripts/obs_release_notes.py
