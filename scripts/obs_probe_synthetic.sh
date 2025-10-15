#!/usr/bin/env bash
set -euo pipefail
EVI="out/obs_gatecheck/evidence"; mkdir -p "$EVI"
URL="${CE_URL:-http://127.0.0.1:8888}"; N=${N:-10}
OK=0; TOTAL=0
probe() { local r="$1"; if curl -fsS "$URL/$r" >/dev/null; then OK=$((OK+1)); fi; TOTAL=$((TOTAL+1)); }
for r in health swap; do i=0; while [ $i -lt $N ]; do probe "$r"; i=$((i+1)); done; done
jq -n --arg url "$URL" --argjson ok $OK --argjson total $TOTAL '{url:$url, ok:$ok, total:$total, ok_ratio: (if $total>0 then ($ok/$total) else 0 end)}' > "$EVI/synthetic_probe.json"
echo PROBE_OK
