#!/usr/bin/env bash
set -euo pipefail
CSV="$1" # saída do twap_compute
viol=0
win=0
while IFS=, read -r ts price tw1 tw5 tw15 div; do
  [[ "$ts" == "ts" ]] && continue
  if [[ $div != "" ]] && awk "BEGIN{exit !($div>1.0)}"; then
    win=$((win+1))
  else
    win=0
  fi
  if [[ $win -ge 2 ]]; then viol=1; break; fi
done < "$CSV"
if [[ $viol -eq 1 ]]; then echo "FREEZE=YES"; else echo "FREEZE=NO"; fi
