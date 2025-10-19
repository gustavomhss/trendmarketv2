#!/usr/bin/env bash
set -euo pipefail
IN="$1"; OUT="$2"
python3 scripts/s3/anti_abuse.py "$IN" >/dev/null
cnt=$(jq length out/s3_gatecheck/abuse_flags.json)
jq -n --argjson c "$cnt" '{hook:"abuse_burst", violation: ($c>0)}' > "$OUT"
