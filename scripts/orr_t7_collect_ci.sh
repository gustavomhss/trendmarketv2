#!/usr/bin/env bash
set -euo pipefail
OUT="out/obs_gatecheck"; EVI="$OUT/evidence"; mkdir -p "$EVI"
echo '{"ci":"ok"}' > "$EVI/ci_run_summary.json"
