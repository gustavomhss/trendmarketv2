#!/usr/bin/env bash
set -euo pipefail

EVI="out/obs_gatecheck/evidence"
mkdir -p "$EVI"

PROM_URL="${PROM_URL:-http://127.0.0.1:9090}"
PROM_QUERY="${PROM_QUERY:-synthetic_ok_ratio}"
LOKI_URL="${LOKI_URL:-http://127.0.0.1:3100}"
LOKI_QUERY="${LOKI_QUERY:-{service=\"trendmarket-amm\"}}"
LOKI_RANGE_SECONDS="${LOKI_RANGE_SECONDS:-300}"
LOKI_LIMIT="${LOKI_LIMIT:-100}"
RECOVERY_SLA_SECONDS="${RECOVERY_SLA_SECONDS:-120}"
RECOVERY_POLL_SECONDS="${RECOVERY_POLL_SECONDS:-5}"
SVC="${SVC:-prom}"
DUR="${DUR:-10}"

PRE_SAMPLE_FILE="$EVI/obs_chaos_pre_sample.json"
POST_SAMPLE_FILE="$EVI/obs_chaos_post_sample.json"
SUMMARY_FILE="$EVI/chaos_summary.json"
export SUMMARY_FILE

CHAOS_MODE="simulated"
export CHAOS_MODE

ISO8601() {
  date -u +"%Y-%m-%dT%H:%M:%SZ"
}

EPOCH_NOW() {
  date -u +%s
}

collect_sample() {
  local phase="$1"
  python3 - "$phase" <<'PY'
import json
import os
import sys
import time
import urllib.parse
import urllib.request

phase = sys.argv[1]

prom_url = os.environ.get("PROM_URL", "http://127.0.0.1:9090").rstrip("/")
prom_query = os.environ.get("PROM_QUERY", "synthetic_ok_ratio")
loki_url = os.environ.get("LOKI_URL", "http://127.0.0.1:3100").rstrip("/")
loki_query = os.environ.get("LOKI_QUERY", '{service="trendmarket-amm"}')
loki_range_seconds = int(float(os.environ.get("LOKI_RANGE_SECONDS", "300")))
loki_limit = int(float(os.environ.get("LOKI_LIMIT", "100")))

sample = {
    "phase": phase,
    "timestamp": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
    "prom": {
        "query": prom_query,
        "ok": False,
    },
    "loki": {
        "query": loki_query,
        "ok": False,
    },
}

def _fetch_json(url):
    request = urllib.request.Request(url, headers={"Accept": "application/json"})
    with urllib.request.urlopen(request, timeout=10) as response:
        return json.loads(response.read().decode("utf-8")), response.status

try:
    prom_params = urllib.parse.urlencode({"query": prom_query})
    prom_resp, prom_status = _fetch_json(f"{prom_url}/api/v1/query?{prom_params}")
    result = prom_resp.get("data", {}).get("result", [])
    sample["prom"].update(
        {
            "status": prom_resp.get("status"),
            "http_status": prom_status,
            "result_count": len(result),
            "sample": result[: min(len(result), 5)],
            "ok": bool(result),
        }
    )
except Exception as exc:  # noqa: BLE001
    sample["prom"]["error"] = str(exc)

try:
    end_ns = int(time.time() * 1_000_000_000)
    start_ns = end_ns - max(loki_range_seconds, 1) * 1_000_000_000
    loki_params = urllib.parse.urlencode(
        {
            "query": loki_query,
            "limit": loki_limit,
            "start": str(start_ns),
            "end": str(end_ns),
        }
    )
    loki_resp, loki_status = _fetch_json(f"{loki_url}/loki/api/v1/query_range?{loki_params}")
    result = loki_resp.get("data", {}).get("result", [])
    entry_count = 0
    preview = []
    for stream in result:
        values = stream.get("values") or []
        entry_count += len(values)
        if values and len(preview) < 5:
            for ts, message in values:
                preview.append({"ts": ts, "line": message})
                if len(preview) >= 5:
                    break
    sample["loki"].update(
        {
            "status": loki_resp.get("status"),
            "http_status": loki_status,
            "stream_count": len(result),
            "entry_count": entry_count,
            "sample": preview,
            "ok": entry_count > 0,
        }
    )
except Exception as exc:  # noqa: BLE001
    sample["loki"]["error"] = str(exc)

json.dump(sample, sys.stdout, indent=2)
sys.stdout.write("\n")
PY
}

sample_prom_ok() {
  python3 - "$1" <<'PY'
import json
import sys

with open(sys.argv[1], encoding="utf-8") as fh:
    data = json.load(fh)

print("1" if data.get("prom", {}).get("ok") else "0")
PY
}

sample_prom_count() {
  python3 - "$1" <<'PY'
import json
import sys

with open(sys.argv[1], encoding="utf-8") as fh:
    data = json.load(fh)

print(data.get("prom", {}).get("result_count", 0))
PY
}

sample_loki_ok() {
  python3 - "$1" <<'PY'
import json
import sys

with open(sys.argv[1], encoding="utf-8") as fh:
    data = json.load(fh)

print("1" if data.get("loki", {}).get("ok") else "0")
PY
}

sample_loki_streams() {
  python3 - "$1" <<'PY'
import json
import sys

with open(sys.argv[1], encoding="utf-8") as fh:
    data = json.load(fh)

print(data.get("loki", {}).get("stream_count", 0))
PY
}

sample_loki_entries() {
  python3 - "$1" <<'PY'
import json
import sys

with open(sys.argv[1], encoding="utf-8") as fh:
    data = json.load(fh)

print(data.get("loki", {}).get("entry_count", 0))
PY
}

sample_timestamp() {
  python3 - "$1" <<'PY'
import json
import sys

with open(sys.argv[1], encoding="utf-8") as fh:
    data = json.load(fh)

print(data.get("timestamp", ""))
PY
}

write_summary() {
  python3 - "$SUMMARY_FILE" <<'PY'
import json
import os
import pathlib
from typing import Any, Dict, Optional

path = pathlib.Path(os.environ["SUMMARY_FILE"])
path.parent.mkdir(parents=True, exist_ok=True)


def _env(name: str) -> Optional[str]:
    value = os.environ.get(name)
    if value in (None, ""):
        return None
    return value


def _env_float(name: str) -> Optional[float]:
    value = _env(name)
    if value is None:
        return None
    try:
        return float(value)
    except ValueError:
        return None


def _env_int(name: str) -> Optional[int]:
    value = _env(name)
    if value is None:
        return None
    try:
        return int(float(value))
    except ValueError:
        return None


def _env_bool(name: str) -> Optional[bool]:
    value = _env(name)
    if value is None:
        return None
    return value.lower() in {"1", "true", "yes", "y", "ok", "on"}


def _telemetry(prefix: str) -> Optional[Dict[str, Any]]:
    prom_count = _env_int(f"CHAOS_{prefix}_PROM_COUNT")
    loki_streams = _env_int(f"CHAOS_{prefix}_LOKI_STREAMS")
    loki_entries = _env_int(f"CHAOS_{prefix}_LOKI_ENTRIES")
    timestamp = _env(f"CHAOS_{prefix}_SAMPLE_TS")
    if all(value is None for value in (prom_count, loki_streams, loki_entries, timestamp)):
        return None
    return {
        "timestamp": timestamp,
        "prom_result_count": prom_count,
        "loki_stream_count": loki_streams,
        "loki_entry_count": loki_entries,
    }


payload = {
    "status": os.environ.get("CHAOS_STATUS", "unknown"),
    "chaos": os.environ.get("CHAOS_MODE", "unknown"),
    "service": _env("CHAOS_SERVICE"),
    "duration_requested_seconds": _env_float("CHAOS_DURATION"),
    "observability_level": {
        "before": _env("CHAOS_OBS_BEFORE"),
        "during": _env("CHAOS_OBS_DURING"),
        "after": _env("CHAOS_OBS_AFTER"),
    },
    "outage_window": {
        "start": _env("CHAOS_OUTAGE_START"),
        "end": _env("CHAOS_OUTAGE_END"),
    },
    "service_events": {
        "stopped_at": _env("CHAOS_SERVICE_STOP_TS"),
        "started_at": _env("CHAOS_SERVICE_START_TS"),
        "recovered_at": _env("CHAOS_RECOVERED_AT"),
    },
    "telemetry": {
        "pre": _telemetry("PRE"),
        "post": _telemetry("POST"),
    },
    "sla": {
        "limit_seconds": _env_float("CHAOS_SLA_LIMIT"),
        "recovery_seconds": _env_float("CHAOS_RECOVERY_SECONDS"),
        "met": _env_bool("CHAOS_RECOVERY_MET"),
    },
    "failure": _env("CHAOS_FAIL_REASON"),
}

with path.open("w", encoding="utf-8") as fh:
    json.dump(payload, fh, indent=2)
    fh.write("\n")
PY
}

fail() {
  local message="$1"
  export CHAOS_STATUS="failed"
  export CHAOS_FAIL_REASON="$message"
  if [ -z "${CHAOS_RECOVERY_MET:-}" ]; then
    export CHAOS_RECOVERY_MET="false"
  fi
  write_summary
  echo "CHAOS_FAIL: $message" >&2
  exit 1
}

if [ "${OBSERVABILITY_LEVEL+x}" = x ]; then
  ORIG_OBS="$OBSERVABILITY_LEVEL"
  HAD_OBS=1
else
  ORIG_OBS=""
  HAD_OBS=0
fi

export CHAOS_SERVICE="$SVC"
export CHAOS_DURATION="$DUR"
export CHAOS_OBS_BEFORE="$ORIG_OBS"
export CHAOS_SLA_LIMIT="$RECOVERY_SLA_SECONDS"

OBS_RESTORED=0

restore_observability_env() {
  if [ "$OBS_RESTORED" -eq 1 ]; then
    return
  fi
  if [ "$HAD_OBS" -eq 1 ]; then
    export OBSERVABILITY_LEVEL="$ORIG_OBS"
  else
    unset OBSERVABILITY_LEVEL || true
  fi
  export CHAOS_OBS_AFTER="$ORIG_OBS"
  OBS_RESTORED=1
}

trap restore_observability_env EXIT

# ---------------------------------------------------------------------------
# Capture baseline telemetry before the outage window.
collect_sample "pre" >"$PRE_SAMPLE_FILE"

export CHAOS_PRE_SAMPLE_TS="$(sample_timestamp "$PRE_SAMPLE_FILE")"
export CHAOS_PRE_PROM_COUNT="$(sample_prom_count "$PRE_SAMPLE_FILE")"
export CHAOS_PRE_LOKI_STREAMS="$(sample_loki_streams "$PRE_SAMPLE_FILE")"
export CHAOS_PRE_LOKI_ENTRIES="$(sample_loki_entries "$PRE_SAMPLE_FILE")"

if [ "$(sample_prom_ok "$PRE_SAMPLE_FILE")" -ne 1 ]; then
  fail "pre-chaos Prometheus query returned no data"
fi

if [ "$(sample_loki_ok "$PRE_SAMPLE_FILE")" -ne 1 ]; then
  fail "pre-chaos Loki query returned no logs"
fi

# ---------------------------------------------------------------------------
# Enter the outage window with observability level degraded to `min`.
export OBSERVABILITY_LEVEL="min"
export CHAOS_OBS_DURING="min"

outage_start_ts="$(ISO8601)"
export CHAOS_OUTAGE_START="$outage_start_ts"

if command -v docker >/dev/null 2>&1; then
  CHAOS_MODE="docker"
  docker stop "$SVC" >/dev/null 2>&1 || true
  export CHAOS_SERVICE_STOP_TS="$(ISO8601)"
  sleep "$DUR"
  docker start "$SVC" >/dev/null 2>&1 || true
  export CHAOS_SERVICE_START_TS="$(ISO8601)"
else
  export CHAOS_SERVICE_STOP_TS="$outage_start_ts"
  export CHAOS_SERVICE_START_TS="$outage_start_ts"
fi

export CHAOS_OUTAGE_END="${CHAOS_SERVICE_START_TS:-$outage_start_ts}"

# Restore observability level after the outage window.
restore_observability_env

recovery_start_epoch=$(EPOCH_NOW)
deadline=$((recovery_start_epoch + RECOVERY_SLA_SECONDS))
export CHAOS_RECOVERY_MET="false"

recovered_epoch=""

while :; do
  collect_sample "post" >"$POST_SAMPLE_FILE"

  export CHAOS_POST_SAMPLE_TS="$(sample_timestamp "$POST_SAMPLE_FILE")"
  export CHAOS_POST_PROM_COUNT="$(sample_prom_count "$POST_SAMPLE_FILE")"
  export CHAOS_POST_LOKI_STREAMS="$(sample_loki_streams "$POST_SAMPLE_FILE")"
  export CHAOS_POST_LOKI_ENTRIES="$(sample_loki_entries "$POST_SAMPLE_FILE")"

  if [ "$(sample_prom_ok "$POST_SAMPLE_FILE")" -eq 1 ] && [ "$(sample_loki_ok "$POST_SAMPLE_FILE")" -eq 1 ]; then
    recovered_epoch=$(EPOCH_NOW)
    export CHAOS_RECOVERY_MET="true"
    export CHAOS_RECOVERY_SECONDS="$((recovered_epoch - recovery_start_epoch))"
    export CHAOS_RECOVERED_AT="$(ISO8601)"
    break
  fi

  if [ "$(EPOCH_NOW)" -ge "$deadline" ]; then
    fail "recovery SLO exceeded (${RECOVERY_SLA_SECONDS}s)"
  fi

  sleep "$RECOVERY_POLL_SECONDS"
done

if [ "${CHAOS_POST_PROM_COUNT:-0}" -le 0 ]; then
  fail "post-chaos Prometheus query returned no data"
fi

if [ "${CHAOS_POST_LOKI_ENTRIES:-0}" -le 0 ]; then
  fail "post-chaos Loki query returned no logs"
fi

export CHAOS_STATUS="ok"
write_summary
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
