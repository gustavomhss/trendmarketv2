#!/usr/bin/env bash
set -euo pipefail

OUT="out/obs_gatecheck"
EVI="$OUT/evidence"
LOG="$OUT/logs"

log() {
  echo "[$(date -u +%H:%M:%S)] $*" | tee -a "$LOG/orr_all.txt"
}

require_cmd() {
  local cmd="$1"
  if ! command -v "$cmd" >/dev/null 2>&1; then
    log "FATAL: required command '$cmd' not found in PATH"
    exit 127
  fi
}

require_script() {
  local label="$1"
  local path="$2"
  if [[ ! -f "$path" ]]; then
    log "FATAL: missing step '$label' script ($path)"
    MISSING=1
  fi
}

run() {
  local n="$1"
  shift
  local script="$1"
  shift || true
  log "→ $n ($script)"
  if [[ "$script" == *.py ]]; then
    python3 "$script" "$@" 2>&1 | tee -a "$LOG/${n}.txt"
  else
    bash "$script" "$@" 2>&1 | tee -a "$LOG/${n}.txt"
  fi
}

main() {
  mkdir -p "$EVI" "$LOG"
  : >"$LOG/orr_all.txt"

  require_cmd bash
  require_cmd python3

  local steps=(
    "T0_env:scripts/orr_env_probe.sh"
    "T1_run:scripts/orr_t1_run.sh"
    "T2_parse:scripts/orr_t2_parse_unit.py"
    "T3_props:scripts/orr_t3_props_run.sh"
    "T4_goldens:scripts/orr_t4_goldens_run.sh"
    "T5_bench:scripts/orr_t5_bench_run.sh"
    "T5_collect:scripts/orr_t5_collect_criterion.py"
    "T6_metrics:scripts/orr_t6_metrics_run.sh"
    "T7_ci_prep:scripts/orr_t7_ci_prep.sh"
    "T7_collect:scripts/orr_t7_collect_ci.sh"
    "T9_pii:scripts/obs_sec_redteam.sh"
    "T10_probe:scripts/obs_probe_synthetic.sh"
    "T11_chaos:scripts/obs_chaos.sh"
    "T12_costs:scripts/obs_cardinality_costs.py"
    "T12_sbom:scripts/obs_sbom.sh"
    "T12_baseline:scripts/obs_baseline_perf.sh"
    "T12_traces:scripts/obs_trace_golden.sh"
    "T8_bundle:scripts/orr_t8_bundle.sh"
    "T9_summary:scripts/orr_t9_summary.sh"
    "T13_release:scripts/obs_release_manifest.py"
    "T14_finalize:scripts/obs_release_finalize.py"
    "T15_notes:scripts/obs_release_notes.py"
  )

  MISSING=0
  local entry
  for entry in "${steps[@]}"; do
    local label=${entry%%:*}
    local path=${entry#*:}
    require_script "$label" "$path"
  done

  if [[ ${MISSING:-0} -ne 0 ]]; then
    log "FATAL: one or more step scripts are missing; aborting"
    exit 127
  fi

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
}

main "$@"
