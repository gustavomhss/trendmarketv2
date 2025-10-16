#!/usr/bin/env bash
set -euo pipefail
EVI="out/obs_gatecheck/evidence"; mkdir -p "$EVI"
echo '{"simulated":true,"alerts_expected":["OBS_P95_Swap_TooHigh","OBS_Hook_Coverage_Low"]}' > "$EVI/watchers_simulation.json"
