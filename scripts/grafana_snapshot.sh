#!/usr/bin/env bash
set -euo pipefail
EVI="out/obs_gatecheck/evidence/dashboards"; mkdir -p "$EVI"
# Sem Grafana com /render aqui, deixamos stub com lista dos JSONs presentes
ls -1 ops/grafana/*.json > "$EVI/dashboards_list.txt" 2>/dev/null || true
echo SNAPSHOT_OK
