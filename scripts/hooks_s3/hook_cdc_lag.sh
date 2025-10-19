#!/usr/bin/env bash
set -euo pipefail
LAG95="$1"; OUT="$2"
viol=0; awk "BEGIN{exit !($LAG95>120)}" || viol=1
jq -n --argjson v "$viol" '{hook:"cdc_lag", violation: ($v==1)}' > "$OUT"
