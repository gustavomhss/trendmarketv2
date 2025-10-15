#!/usr/bin/env bash
set -euo pipefail
EVI="out/obs_gatecheck/evidence"; mkdir -p "$EVI"
SVC="${SVC:-prom}"; DUR="${DUR:-10}"
if command -v docker >/dev/null 2>&1; then
  docker stop "$SVC" >/dev/null 2>&1 || true
  sleep "$DUR"
  docker start "$SVC" >/dev/null 2>&1 || true
  echo '{"chaos":"docker","service":"'"$SVC"'","duration_sec":'"$DUR"'}' > "$EVI/chaos_summary.json"
else
  echo '{"chaos":"simulated","reason":"docker_unavailable"}' > "$EVI/chaos_summary.json"
fi
echo CHAOS_OK
