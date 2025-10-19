#!/usr/bin/env bash
set -euo pipefail
DEPTH="$1"; OUT="$2"
val=$(cat "$DEPTH")
viol=0; awk "BEGIN{exit !($val<500)}" || viol=1
jq -n --argjson v "$viol" '{hook:"liquidity_depth_gap", violation: ($v==1)}' > "$OUT"
