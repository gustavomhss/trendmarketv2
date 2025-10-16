#!/usr/bin/env bash
set -euo pipefail
OUT="out/obs_gatecheck"; EVI="$OUT/evidence"; mkdir -p "$EVI"
# Encadeia o resultado do probe como T1
[ -f "$EVI/t1_scan.json" ] || echo '{"prom":"UNKNOWN"}' > "$EVI/t1_scan.json"
