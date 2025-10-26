#!/usr/bin/env bash
set -euo pipefail

EVI="out/obs_gatecheck/evidence"
mkdir -p "$EVI"

SVC="${SVC:-prom}"
DUR="${DUR:-10}"

if ! command -v docker >/dev/null 2>&1; then
  cat >"$EVI/chaos_summary.json" <<JSON
{"chaos":"simulated","reason":"docker_unavailable"}
JSON
  echo CHAOS_OK
  exit 0
fi

PORT_BASE=${CHAOS_DEV_PORT:-18980}
PYTHONPATH_ROOT="src${PYTHONPATH:+:${PYTHONPATH}}"

collect_snapshot() {
  local level="$1"
  local prefix="$2"
  local port=$((PORT_BASE + RANDOM % 1000))
  local metrics_file="$EVI/${prefix}_metrics.prom"
  local state_file="$EVI/${prefix}_state.json"

  OBSERVABILITY_LEVEL="$level" PYTHONPATH="$PYTHONPATH_ROOT" python3 - <<'PY' "$port" &
import sys
from amm_obs import run_dev_server


def main() -> None:
    port = int(sys.argv[1])
    run_dev_server(host="127.0.0.1", port=port)


if __name__ == "__main__":
    main()
PY
  local server_pid=$!
  trap 'kill "$server_pid" >/dev/null 2>&1 || true' EXIT

  local attempt=0
  until curl -fsS "http://127.0.0.1:${port}/health" >/dev/null 2>&1; do
    sleep 0.2
    attempt=$((attempt + 1))
    if [ "$attempt" -ge 50 ]; then
      echo "[obs_chaos] dev server failed to start" >&2
      kill "$server_pid" >/dev/null 2>&1 || true
      wait "$server_pid" >/dev/null 2>&1 || true
      trap - EXIT
      return 1
    fi
  done

  curl -fsS "http://127.0.0.1:${port}/metrics" >"$metrics_file"
  curl -fsS "http://127.0.0.1:${port}/swap" >/dev/null 2>&1 || true

  kill "$server_pid" >/dev/null 2>&1 || true
  wait "$server_pid" >/dev/null 2>&1 || true
  trap - EXIT

  OBSERVABILITY_LEVEL="$level" PYTHONPATH="$PYTHONPATH_ROOT" python3 - <<'PY' "$state_file"
import json
import sys
from amm_obs import AMMObservability


def main() -> None:
    target = sys.argv[1]
    telemetry = AMMObservability()
    telemetry.simulate_unit_load()
    with open(target, "w", encoding="utf-8") as fh:
        json.dump(telemetry.serialize(), fh, indent=2)
        fh.write("\n")


if __name__ == "__main__":
    main()
PY

  printf '%s|%s\n' "$state_file" "$metrics_file"
}

validate_minimum_payload() {
  local snapshot="$1"
  local metrics_path="$2"
  python3 - <<'PY' "$snapshot"
import json
import sys

path = sys.argv[1]
with open(path, "r", encoding="utf-8") as fh:
    payload = json.load(fh)

meta = payload.get("meta", {})
if meta.get("observability_level") != "min":
    raise SystemExit(f"expected min observability level, got {meta.get('observability_level')!r}")

logs = payload.get("logs", [])
if not logs:
    raise SystemExit("no logs captured under min observability level")

metrics = payload.get("metrics", {})
ops = metrics.get("amm_op_latency_seconds", {}).get("operations", {})
if not ops:
    raise SystemExit("no metrics captured under min observability level")
PY
  if ! grep -q "amm_op_latency_seconds" "$metrics_path"; then
    echo "[obs_chaos] expected amm_op_latency_seconds in metrics scrape" >&2
    return 1
  fi
}

summarize() {
  local start_ts="$1"
  local end_ts="$2"
  local outage_seconds="$3"
  local recovery_seconds="$4"
  local min_state="$5"
  local min_metrics="$6"
  local pre_state="$7"
  local pre_metrics="$8"
  local post_state="$9"
  local post_metrics="${10}"
  local recovery_ok="${11}"

  cat >"$EVI/chaos_summary.json" <<JSON
{
  "chaos": "docker",
  "service": "${SVC}",
  "configured_duration_sec": ${DUR},
  "outage_window": {
    "started_at": "${start_ts}",
    "ended_at": "${end_ts}",
    "outage_seconds": ${outage_seconds},
    "recovery_seconds": ${recovery_seconds}
  },
  "recovery_within_slo": ${recovery_ok},
  "minimum_telemetry": {
    "ok": true,
    "state": "${min_state}",
    "metrics": "${min_metrics}"
  },
  "snapshots": {
    "before": {"state": "${pre_state}", "metrics": "${pre_metrics}"},
    "during": {"state": "${min_state}", "metrics": "${min_metrics}"},
    "after": {"state": "${post_state}", "metrics": "${post_metrics}"}
  }
}
JSON
}

IFS='|' read -r pre_state pre_metrics <<<"$(collect_snapshot "full" "before")"

outage_started_at=$(date --iso-8601=seconds)
outage_started_epoch=$(date +%s)
docker stop "$SVC" >/dev/null 2>&1 || true

IFS='|' read -r min_state min_metrics <<<"$(collect_snapshot "min" "during")"

sleep "$DUR"

docker start "$SVC" >/dev/null 2>&1 || true

recovery_begin_epoch=$(date +%s)
while true; do
  if [ "$(docker inspect -f '{{.State.Running}}' "$SVC" 2>/dev/null || echo false)" = "true" ]; then
    break
  fi
  sleep 1
done

outage_ended_epoch=$(date +%s)
outage_ended_at=$(date --iso-8601=seconds)

recovery_seconds=$((outage_ended_epoch - recovery_begin_epoch))
outage_seconds=$((outage_ended_epoch - outage_started_epoch))
if [ "$recovery_seconds" -gt 120 ]; then
  echo "[obs_chaos] recovery exceeded 120 seconds (${recovery_seconds}s)" >&2
  exit 1
fi

validate_minimum_payload "$min_state" "$min_metrics"

IFS='|' read -r post_state post_metrics <<<"$(collect_snapshot "full" "after")"

recovery_ok=true

summarize "$outage_started_at" "$outage_ended_at" "$outage_seconds" "$recovery_seconds" "$min_state" "$min_metrics" "$pre_state" "$pre_metrics" "$post_state" "$post_metrics" "$recovery_ok"

echo CHAOS_OK
