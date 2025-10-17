#!/usr/bin/env bash
set -euo pipefail
OUT="out/obs_gatecheck"; EVI="$OUT/evidence"; LOG="$OUT/logs"; mkdir -p "$EVI" "$LOG"
log(){ echo "[$(date -u +%H:%M:%S)] $*" | tee -a "$LOG/orr_all.txt"; }
run(){ local n="$1"; shift; log "→ $n"; bash "$@" 2>&1 | tee -a "$LOG/${n}.txt"; }


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
run T8_bundle scripts/orr_t8_bundle.sh


log "ACCEPTANCE_OK"; echo ACCEPTANCE_OK
log "GATECHECK_OK"; echo GATECHECK_OK
