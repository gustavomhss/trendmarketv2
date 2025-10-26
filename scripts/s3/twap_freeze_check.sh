#!/usr/bin/env bash
set -euo pipefail
CSV="${1:?need twap csv}" # saída do twap_compute
EVENTS="${2:?need twap events json}" # twap_events.json
EVID_DIR="$(dirname "$CSV")"
[[ -d "$EVID_DIR" ]] || mkdir -p "$EVID_DIR"

divergence_freeze=0
streak=0
while IFS=, read -r ts price tw1 tw5 tw15 div; do
  [[ "$ts" == "ts" ]] && continue
  if [[ -n "$div" ]] && awk "BEGIN{exit !($div>1.0)}"; then
    streak=$((streak+1))
  else
    streak=0
  fi
  if [[ $streak -ge 2 ]]; then divergence_freeze=1; break; fi
done < "$CSV"

ic_exceed_count=$(python3 - "$EVENTS" <<'PY'
import json, sys, pathlib
p = pathlib.Path(sys.argv[1])
if p.exists():
    data = json.loads(p.read_text(encoding='utf-8'))
else:
    data = []
print(sum(1 for item in data if item.get('ic99_exceeded')))
PY
)

freeze_reason=""
if [[ $divergence_freeze -eq 1 ]]; then
  freeze_reason="divergence"
elif [[ $ic_exceed_count -ge 3 ]]; then
  freeze_reason="ic99"
fi

if [[ -n "$freeze_reason" ]]; then
  verdict="YES"
else
  verdict="NO"
fi

cat >"$EVID_DIR/twap_freeze.json" <<JSON
{
  "freeze": "$verdict",
  "reason": "$freeze_reason",
  "ic99_exceeded": $ic_exceed_count,
  "divergence_streak": $streak
}
JSON

echo "FREEZE=$verdict"
