#!/usr/bin/env bash
set -euo pipefail
EVI="out/obs_gatecheck/evidence"; mkdir -p "$EVI"
cat > "$EVI/watchers_simulation.json" <<'JSON'
{
  "simulated": true,
  "alerts_expected": [
    {"alert": "OBS_P95_Swap_TooHigh", "reason": "p95 swap > 60ms durante rampa sintética"},
    {"alert": "OBS_Oracle_Stale", "reason": "freshness oracle > 5s por 10m"},
    {"alert": "OBS_CDC_Lag_Warn", "reason": "stream orders com lag > 10s"},
    {"alert": "OBS_Drift_Critical_Feature_Warn", "reason": "drift_score price_psi acima de 0.2"},
    {"alert": "OBS_Hook_Coverage_Low", "reason": "hook_coverage_ratio abaixo de 0.95"},
    {"alert": "OBS_Hook_Execution_Stalled", "reason": "hook_pre_trade sem execuções em 1h"},
    {"alert": "OBS_Cardinality_Budget_Warn", "reason": "observability_series_budget_ratio > 0.7"},
    {"alert": "OBS_Cardinality_Budget_Crit", "reason": "observability_series_budget_ratio > 0.9"}
  ]
}
JSON
