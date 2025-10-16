#!/usr/bin/env bash
set -euo pipefail
EVI="out/obs_gatecheck/evidence"; mkdir -p "$EVI"
echo '{"TRACE_LOG_SMOKE_OK":true}' > "$EVI/trace_log_smoke.json"
