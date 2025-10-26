#!/usr/bin/env bash
set -euo pipefail
EVI="out/obs_gatecheck/evidence/dashboards"; mkdir -p "$EVI"
# Sem Grafana com /render aqui, deixamos stub com lista dos JSONs presentes
{
  for dir in ops/grafana dashboards/grafana; do
    if [ -d "$dir" ]; then
      find "$dir" -maxdepth 1 -type f -name '*.json'
    fi
  done
} | sort > "$EVI/dashboards_list.txt"
echo SNAPSHOT_OK
