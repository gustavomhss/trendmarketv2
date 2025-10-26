#!/usr/bin/env bash
set -euo pipefail
EVI="out/obs_gatecheck/evidence/dashboards"
mkdir -p "$EVI"
: > "$EVI/dashboards_list.txt"

for dir in ops/grafana dashboards/grafana; do
  if [ -d "$dir" ]; then
    while IFS= read -r file; do
      echo "$file" >> "$EVI/dashboards_list.txt"
      dest="$EVI/$file"
      mkdir -p "$(dirname "$dest")"
      cp "$file" "$dest"
    done < <(find "$dir" -maxdepth 1 -type f -name '*.json' | sort)
  fi
done

echo SNAPSHOT_OK
