#!/usr/bin/env bash
set -euo pipefail
EVI="out/obs_gatecheck/evidence"; mkdir -p "$EVI"
URL="${CE_URL:-http://127.0.0.1:8888}"; N=${N:-10}
OK=0; TOTAL=0
probe() {
  local r="$1"
  if curl -fsS "$URL/$r" >/dev/null 2>&1; then
    OK=$((OK+1))
  fi
  TOTAL=$((TOTAL+1))
}
for r in health swap; do
  i=0
  while [ $i -lt $N ]; do
    probe "$r"
    i=$((i+1))
  done
done

OUTPUT="$EVI/synthetic_probe.json"
export URL OUTPUT OK TOTAL

python3 - <<PY
import json, os
path = os.environ["OUTPUT"]
ok = int(os.environ.get("OK", "0"))
total = int(os.environ.get("TOTAL", "0"))
ratio = (ok / total) if total else 0.0
payload = {
    "url": os.environ["URL"],
    "ok": ok,
    "total": total,
    "ok_ratio": round(ratio, 4),
}
with open(path, "w", encoding="utf-8") as fh:
    json.dump(payload, fh, indent=2)
    fh.write("\n")
PY
echo PROBE_OK
