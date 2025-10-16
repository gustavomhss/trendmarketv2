#!/usr/bin/env bash
set -euo pipefail
EVI="out/obs_gatecheck/evidence"; mkdir -p "$EVI"
echo '{"ci":"prep"}' > "$EVI/ci_prep.json"
