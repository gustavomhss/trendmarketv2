#!/usr/bin/env bash
set -euo pipefail
HOURS="$1"; OUT="$2"
viol=0; awk "BEGIN{exit !($HOURS>24)}" || viol=1
jq -n --argjson v "$viol" '{hook:"resolution_sla_breach", violation: ($v==1)}' > "$OUT"
