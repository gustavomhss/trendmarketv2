#!/usr/bin/env bash
set -euo pipefail
EVI="out/obs_gatecheck/evidence"; mkdir -p "$EVI"
URL="${CE_URL:-http://127.0.0.1:8888}"; N=${N:-10}
OK=0; TOTAL=0

STARTED_SERVER=0
SERVER_PID=""

cleanup() {
  if [ "$STARTED_SERVER" -eq 1 ] && [ -n "$SERVER_PID" ]; then
    kill "$SERVER_PID" >/dev/null 2>&1 || true
    wait "$SERVER_PID" >/dev/null 2>&1 || true
  fi
}

trap cleanup EXIT

# Boot the deterministic dev server when no synthetic endpoint is available.
if ! curl -fsS "$URL/health" >/dev/null 2>&1; then
  PYTHONPATH=src python3 - <<'PY' "$URL" &
import sys
from urllib.parse import urlparse

from amm_obs import run_dev_server


def main() -> None:
    parsed = urlparse(sys.argv[1])
    host = parsed.hostname or "127.0.0.1"
    port = parsed.port or 8888
    run_dev_server(host=host, port=port)


if __name__ == "__main__":
    main()
PY
  SERVER_PID=$!
  STARTED_SERVER=1
  # Give the background server a moment to bind the socket.
  for _ in $(seq 1 10); do
    if curl -fsS "$URL/health" >/dev/null 2>&1; then
      break
    fi
    sleep 0.2
  done
fi
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
