#!/usr/bin/env bash
set -euo pipefail

EVI="out/obs_gatecheck/evidence"
mkdir -p "$EVI"

ARCH=$(uname -m 2>/dev/null || echo unknown)
BASELINE_SAMPLES=${BASELINE_SAMPLES:-40}
BASELINE_ROUTES=${BASELINE_ROUTES:-"health swap"}
BASELINE_WARMUP=${BASELINE_WARMUP:-5}
BASELINE_TIMEOUT=${BASELINE_TIMEOUT:-2.0}
RESULT_JSON="$EVI/baseline_perf.json"
RESULT_CSV="$EVI/baseline_perf.csv"

SERVER_PIDS=()
TMP_FILES=()

cleanup() {
  for pid in "${SERVER_PIDS[@]:-}"; do
    if [ -n "$pid" ]; then
      kill "$pid" >/dev/null 2>&1 || true
      wait "$pid" >/dev/null 2>&1 || true
    fi
  done
  for file in "${TMP_FILES[@]:-}"; do
    [ -z "$file" ] && continue
    rm -f "$file"
  done
}

trap cleanup EXIT

pick_free_port() {
  python3 - <<'PY'
import socket
with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as sock:
    sock.bind(("127.0.0.1", 0))
    print(sock.getsockname()[1])
PY
}

LAST_SERVER_PID=""

start_server() {
  local level="$1"
  local port="$2"
  OBSERVABILITY_LEVEL="$level" PYTHONPATH=src python3 - <<'PY' "$port" &
import sys
from amm_obs import run_dev_server

def main() -> None:
    port = int(sys.argv[1])
    run_dev_server(host="127.0.0.1", port=port)

if __name__ == "__main__":
    main()
PY
  LAST_SERVER_PID=$!
  SERVER_PIDS+=("$LAST_SERVER_PID")
}

wait_for_server() {
  local port="$1"
  local attempts=60
  local url="http://127.0.0.1:${port}/health"
  while [ $attempts -gt 0 ]; do
    if curl -fsS --max-time 2 "$url" >/dev/null 2>&1; then
      return 0
    fi
    sleep 0.2
    attempts=$((attempts - 1))
  done
  return 1
}

run_profile() {
  local level="$1"
  local port="$2"
  local output="$3"
  TARGET_URL="http://127.0.0.1:${port}" \
  PROFILE_LEVEL="$level" \
  PROFILE_SAMPLES="$BASELINE_SAMPLES" \
  PROFILE_ROUTES="$BASELINE_ROUTES" \
  PROFILE_TIMEOUT="$BASELINE_TIMEOUT" \
  PROFILE_WARMUP="$BASELINE_WARMUP" \
  python3 - <<'PY' > "$output"
import json
import math
import os
import statistics
import sys
import time
import urllib.error
import urllib.request
from datetime import datetime, timezone

base_url = os.environ.get("TARGET_URL", "http://127.0.0.1:8888").rstrip("/")
level = os.environ.get("PROFILE_LEVEL", "full")
try:
    samples = int(os.environ.get("PROFILE_SAMPLES", "40"))
except ValueError:
    samples = 40
try:
    warmup = int(os.environ.get("PROFILE_WARMUP", "5"))
except ValueError:
    warmup = 5
try:
    timeout = float(os.environ.get("PROFILE_TIMEOUT", "2.0"))
except ValueError:
    timeout = 2.0
routes_raw = os.environ.get("PROFILE_ROUTES", "health swap")
routes = [r.strip() for r in routes_raw.split() if r.strip()]
if not routes:
    routes = ["health"]

opener = urllib.request.build_opener()
opener.addheaders = [("User-Agent", "baseline-perf-probe/1.0")]

def call_route(route: str, record_latency: bool) -> float:
    url = base_url if route in {"", "/"} else f"{base_url}/{route.strip('/')}"
    start = time.perf_counter()
    try:
        with opener.open(url, timeout=timeout) as resp:
            resp.read()
            if resp.getcode() != 200:
                return math.nan
    except urllib.error.URLError:
        return math.nan
    except TimeoutError:
        return math.nan
    except Exception:
        return math.nan
    end = time.perf_counter()
    duration_ms = (end - start) * 1000.0
    return duration_ms if record_latency else math.nan

# Warm-up phase
for _ in range(max(warmup, 0)):
    call_route(routes[0], record_latency=False)

latencies: list[float] = []
errors = 0
success = 0
requests_total = len(routes) * samples if samples > 0 else 0
start_wall = time.perf_counter()
start_cpu = time.process_time()

for route in routes:
    for _ in range(samples):
        latency_ms = call_route(route, record_latency=True)
        if math.isnan(latency_ms):
            errors += 1
            continue
        success += 1
        latencies.append(latency_ms)

wall_seconds = time.perf_counter() - start_wall
cpu_seconds = time.process_time() - start_cpu
latency_samples = len(latencies)

if latency_samples:
    latencies.sort()
    index = max(0, math.ceil(0.95 * latency_samples) - 1)
    p95_ms = latencies[index]
    mean_ms = statistics.fmean(latencies)
    median_ms = statistics.median(latencies)
    min_ms = latencies[0]
    max_ms = latencies[-1]
else:
    p95_ms = 0.0
    mean_ms = 0.0
    median_ms = 0.0
    min_ms = 0.0
    max_ms = 0.0

success_ratio = (success / requests_total) if requests_total else 0.0
throughput_rps = (success / wall_seconds) if wall_seconds > 1e-12 else 0.0
cpu_pct = (cpu_seconds / wall_seconds * 100.0) if wall_seconds > 1e-12 else 0.0

def r(value: float) -> float:
    return round(float(value), 4)

payload = {
    "level": level,
    "url": base_url,
    "routes": routes,
    "timestamp": datetime.now(timezone.utc).isoformat(),
    "samples_per_route": samples,
    "requests_total": requests_total,
    "success_count": success,
    "error_count": errors,
    "latency_samples": latency_samples,
    "success_ratio": r(success_ratio),
    "p95_ms": r(p95_ms),
    "mean_ms": r(mean_ms),
    "median_ms": r(median_ms),
    "min_ms": r(min_ms),
    "max_ms": r(max_ms),
    "wall_seconds": r(wall_seconds),
    "cpu_seconds": r(cpu_seconds),
    "cpu_pct": r(cpu_pct),
    "throughput_rps": r(throughput_rps),
    "timeout_seconds": timeout,
}

with open(sys.stdout.fileno(), "w", encoding="utf-8", closefd=False) as fh:
    json.dump(payload, fh, indent=2)
    fh.write("\n")
PY
}

levels=(min full)
profile_files=()

for level in "${levels[@]}"; do
  port=$(pick_free_port)
  start_server "$level" "$port"
  server_pid="$LAST_SERVER_PID"
  if ! wait_for_server "$port"; then
    echo "failed to start dev server for level $level" >&2
    exit 1
  fi
  tmp_profile=$(mktemp)
  TMP_FILES+=("$tmp_profile")
  run_profile "$level" "$port" "$tmp_profile"
  kill "$server_pid" >/dev/null 2>&1 || true
  wait "$server_pid" >/dev/null 2>&1 || true
  profile_files+=("$tmp_profile")
done

MIN_PROFILE=${profile_files[0]}
FULL_PROFILE=${profile_files[1]}

set +e
ARCH="$ARCH" python3 - <<'PY' "$MIN_PROFILE" "$FULL_PROFILE" "$RESULT_JSON" "$RESULT_CSV"
import csv
import json
import math
import os
import sys
from datetime import datetime, timezone
from typing import Any, Dict, Optional

min_path, full_path, dest_path, csv_path = sys.argv[1:5]
arch = os.environ.get("ARCH", "unknown")
now = datetime.now(timezone.utc).isoformat()

with open(min_path, "r", encoding="utf-8") as fh:
    min_profile = json.load(fh)
with open(full_path, "r", encoding="utf-8") as fh:
    full_profile = json.load(fh)

for profile, level in ((min_profile, "min"), (full_profile, "full")):
    profile.setdefault("level", level)
    profile.setdefault("arch", arch)

cpu_delta = float(full_profile.get("cpu_seconds", 0.0)) - float(min_profile.get("cpu_seconds", 0.0))
p95_delta = float(full_profile.get("p95_ms", 0.0)) - float(min_profile.get("p95_ms", 0.0))
throughput_delta = float(full_profile.get("throughput_rps", 0.0)) - float(min_profile.get("throughput_rps", 0.0))

min_cpu = float(min_profile.get("cpu_seconds", 0.0))
min_p95 = float(min_profile.get("p95_ms", 0.0))
min_throughput = float(min_profile.get("throughput_rps", 0.0))


def pct(delta: float, baseline: float) -> float:
    if math.isfinite(baseline) and abs(baseline) > 1e-12:
        return delta / baseline * 100.0
    if abs(delta) <= 1e-12:
        return 0.0
    return math.inf if delta > 0 else -math.inf

cpu_overhead_pct = pct(cpu_delta, min_cpu)
p95_delta_pct = pct(p95_delta, min_p95)
throughput_delta_pct = pct(throughput_delta, min_throughput)
cpu_pct_delta = float(full_profile.get("cpu_pct", 0.0)) - float(min_profile.get("cpu_pct", 0.0))


def safe_round(value: Optional[float], digits: int = 4) -> Optional[float]:
    if value is None:
        return None
    try:
        num = float(value)
    except (TypeError, ValueError):
        return None
    if not math.isfinite(num):
        return None
    return round(num, digits)

entry: Dict[str, Any] = {
    "arch": arch,
    "timestamp": now,
    "profiles": {
        "min": min_profile,
        "full": full_profile,
    },
    "deltas": {
        "cpu_delta_seconds": safe_round(cpu_delta, 4),
        "cpu_overhead_pct": safe_round(cpu_overhead_pct, 4),
        "p95_delta_ms": safe_round(p95_delta, 4),
        "p95_delta_pct": safe_round(p95_delta_pct, 4),
        "throughput_delta_pct": safe_round(throughput_delta_pct, 4),
        "cpu_pct_delta": safe_round(cpu_pct_delta, 4),
    },
}

status = "pass"
if entry["deltas"]["cpu_overhead_pct"] is None or entry["deltas"]["cpu_overhead_pct"] > 3:
    status = "fail"
if entry["deltas"]["p95_delta_pct"] is None or entry["deltas"]["p95_delta_pct"] > 5:
    status = "fail"
entry["status"] = status

existing: Dict[str, Any] = {}
if os.path.exists(dest_path):
    try:
        with open(dest_path, "r", encoding="utf-8") as fh:
            loaded = json.load(fh)
        if isinstance(loaded, dict):
            existing = loaded
    except json.JSONDecodeError:
        existing = {}

results = existing.get("results")
if not isinstance(results, dict):
    results = {}
results[arch] = entry
existing["results"] = results
existing["generated_at"] = now
existing["schema_version"] = 1

comparisons = existing.get("comparisons")
if not isinstance(comparisons, dict):
    comparisons = {}

if "arm64" in results and "x86_64" in results:
    arm_entry = results["arm64"]
    x86_entry = results["x86_64"]

    def get_profile(entry_data: Dict[str, Any], level: str) -> Dict[str, Any]:
        profiles = entry_data.get("profiles")
        if isinstance(profiles, dict):
            profile = profiles.get(level)
            if isinstance(profile, dict):
                return profile
        return {}

    def extract(profile: Dict[str, Any], key: str) -> Optional[float]:
        if not isinstance(profile, dict):
            return None
        value = profile.get(key)
        if value is None:
            return None
        try:
            num = float(value)
        except (TypeError, ValueError):
            return None
        return num if math.isfinite(num) else None

    pair: Dict[str, Any] = {"generated_at": now}
    for lvl in ("min", "full"):
        arm_profile = get_profile(arm_entry, lvl)
        x86_profile = get_profile(x86_entry, lvl)
        arm_p95 = extract(arm_profile, "p95_ms")
        x86_p95 = extract(x86_profile, "p95_ms")
        arm_cpu_pct = extract(arm_profile, "cpu_pct")
        x86_cpu_pct = extract(x86_profile, "cpu_pct")
        arm_throughput = extract(arm_profile, "throughput_rps")
        x86_throughput = extract(x86_profile, "throughput_rps")

        comparison = {
            "p95_ms_arm64": arm_p95,
            "p95_ms_x86_64": x86_p95,
            "p95_delta_pct": safe_round(pct((arm_p95 or 0.0) - (x86_p95 or 0.0), x86_p95 or 0.0), 4),
            "cpu_pct_arm64": arm_cpu_pct,
            "cpu_pct_x86_64": x86_cpu_pct,
            "cpu_pct_delta": safe_round((arm_cpu_pct - x86_cpu_pct) if (arm_cpu_pct is not None and x86_cpu_pct is not None) else None, 4),
            "throughput_rps_arm64": arm_throughput,
            "throughput_rps_x86_64": x86_throughput,
            "throughput_delta_pct": safe_round(pct((arm_throughput or 0.0) - (x86_throughput or 0.0), x86_throughput or 0.0), 4),
        }
        pair[lvl] = comparison
    comparisons["arm64_vs_x86_64"] = pair
else:
    comparisons.pop("arm64_vs_x86_64", None)

existing["comparisons"] = comparisons

for legacy in ("host", "p95_ms", "cpu_overhead_pct"):
    existing.pop(legacy, None)

with open(dest_path, "w", encoding="utf-8") as fh:
    json.dump(existing, fh, indent=2)
    fh.write("\n")

if csv_path:
    headers = [
        "arch",
        "level",
        "observability_level",
        "timestamp",
        "p95_ms",
        "mean_ms",
        "median_ms",
        "success_ratio",
        "requests_total",
        "success_count",
        "error_count",
        "latency_samples",
        "throughput_rps",
        "cpu_seconds",
        "wall_seconds",
        "cpu_pct",
    ]
    with open(csv_path, "w", encoding="utf-8", newline="") as csvfile:
        writer = csv.writer(csvfile)
        writer.writerow(headers)
        for arch_key, arch_entry in sorted(existing["results"].items()):
            profiles = arch_entry.get("profiles")
            if not isinstance(profiles, dict):
                continue
            for lvl in ("min", "full"):
                profile = profiles.get(lvl)
                if not isinstance(profile, dict):
                    continue
                writer.writerow([
                    arch_key,
                    lvl,
                    profile.get("level"),
                    profile.get("timestamp"),
                    profile.get("p95_ms"),
                    profile.get("mean_ms"),
                    profile.get("median_ms"),
                    profile.get("success_ratio"),
                    profile.get("requests_total"),
                    profile.get("success_count"),
                    profile.get("error_count"),
                    profile.get("latency_samples"),
                    profile.get("throughput_rps"),
                    profile.get("cpu_seconds"),
                    profile.get("wall_seconds"),
                    profile.get("cpu_pct"),
                ])

summary_cpu = entry["deltas"].get("cpu_overhead_pct")
summary_p95 = entry["deltas"].get("p95_delta_pct")

def fmt(value: Optional[float]) -> str:
    if value is None:
        return "nan"
    return f"{value:.2f}"

message = f"[baseline] arch={arch} cpu_overhead_pct={fmt(summary_cpu)} p95_delta_pct={fmt(summary_p95)} status={status}"
if status == "pass":
    print(message)
    sys.exit(0)
print(message, file=sys.stderr)
sys.exit(1)
PY
status=$?
set -e
if [ $status -ne 0 ]; then
  echo BASELINE_FAIL
  exit $status
fi

echo BASELINE_OK
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$SCRIPT_DIR/.."
EVI="$ROOT/out/obs_gatecheck/evidence"
mkdir -p "$EVI"

ARCH=$(uname -m || echo unknown)
ITERATIONS=${OBS_BASELINE_ITERATIONS:-500}
CPU_LIMIT=${OBS_BASELINE_CPU_LIMIT:-3}
LAT_LIMIT=${OBS_BASELINE_LATENCY_LIMIT:-5}
OUTPUT="$EVI/baseline_perf.json"

export OBS_BASELINE_ARCH="$ARCH"
export OBS_BASELINE_ITERATIONS="$ITERATIONS"
export OBS_BASELINE_CPU_LIMIT="$CPU_LIMIT"
export OBS_BASELINE_LATENCY_LIMIT="$LAT_LIMIT"
export PYTHONPATH="$ROOT/src${PYTHONPATH:+:$PYTHONPATH}"

TMP_FILE="${OUTPUT}.tmp"

python3 - <<'PY' > "$TMP_FILE"
import json
import math
import os
import sys
import time
from datetime import datetime, timezone

from amm_obs import AMMObservability


def percentile(values, quantile):
    if not values:
        return 0.0
    ordered = sorted(values)
    pos = (len(ordered) - 1) * quantile
    lower = math.floor(pos)
    upper = math.ceil(pos)
    if lower == upper:
        return ordered[int(pos)]
    low = ordered[lower]
    high = ordered[upper]
    return (low * (upper - pos)) + (high * (pos - lower))


arch = os.environ.get("OBS_BASELINE_ARCH", "unknown")
iterations = int(os.environ.get("OBS_BASELINE_ITERATIONS", "500"))
cpu_limit = float(os.environ.get("OBS_BASELINE_CPU_LIMIT", "3"))
lat_limit = float(os.environ.get("OBS_BASELINE_LATENCY_LIMIT", "5"))

profiles = {}

for level in ("min", "full"):
    obs = AMMObservability(observability_level=level)
    start_cpu = time.process_time()
    start_wall = time.perf_counter()
    for _ in range(iterations):
        obs.simulate_unit_load()
    wall_time = time.perf_counter() - start_wall
    cpu_time = time.process_time() - start_cpu

    latencies = [
        latency
        for series in obs._latency_records.values()  # noqa: SLF001 (internal for diagnostics)
        for latency in series
    ]
    p95_seconds = percentile(latencies, 0.95)

    metrics = obs.metrics_snapshot()
    operations = {}
    total_ops = 0
    for op, payload in sorted(metrics.get("operations", {}).items()):
        count = int(payload.get("count", 0))
        operations[op] = {
            "count": count,
            "avg_ms": round(float(payload.get("avg", 0.0)) * 1000, 3),
            "p95_ms": round(float(payload.get("p95", 0.0)) * 1000, 3),
        }
        total_ops += count

    profiles[level] = {
        "observability_level": level,
        "iterations": iterations,
        "wall_time_seconds": round(wall_time, 6),
        "cpu_seconds": round(cpu_time, 6),
        "latency_p95_ms": round(p95_seconds * 1000, 3),
        "total_operations": total_ops,
        "operations": operations,
    }

cpu_min = profiles["min"]["cpu_seconds"]
cpu_full = profiles["full"]["cpu_seconds"]
lat_min = profiles["min"]["latency_p95_ms"]
lat_full = profiles["full"]["latency_p95_ms"]

cpu_overhead_pct = None
if cpu_min > 0:
    cpu_overhead_pct = round(((cpu_full - cpu_min) / cpu_min) * 100.0, 3)

latency_delta_ms = round(lat_full - lat_min, 3)
latency_delta_pct = None
if lat_min > 0:
    latency_delta_pct = round(((lat_full - lat_min) / lat_min) * 100.0, 3)

violations = []
if cpu_overhead_pct is None:
    violations.append("cpu_overhead_unavailable")
elif cpu_overhead_pct > cpu_limit:
    violations.append(f"cpu_overhead_pct>{cpu_limit}")

if latency_delta_pct is None:
    violations.append("latency_delta_unavailable")
elif abs(latency_delta_pct) > lat_limit:
    violations.append(f"latency_delta_pct>{lat_limit}")

result = {
    "host": arch,
    "generated_at": datetime.now(timezone.utc).isoformat().replace("+00:00", "Z"),
    "iterations": iterations,
    "profiles": profiles,
    "thresholds": {
        "cpu_overhead_pct": cpu_limit,
        "latency_p95_delta_pct": lat_limit,
    },
    "deltas": {
        "cpu_overhead_pct": cpu_overhead_pct,
        "latency_p95_delta_pct": latency_delta_pct,
        "latency_p95_delta_ms": latency_delta_ms,
    },
    "status": "pass" if not violations else "fail",
    "violations": violations,
}

json.dump(result, sys.stdout, indent=2, sort_keys=True)
sys.stdout.write("\n")
PY

mv "$TMP_FILE" "$OUTPUT"

STATUS=$(jq -r '.status' "$OUTPUT")
if [[ "$STATUS" == "pass" ]]; then
  echo BASELINE_OK
else
  REASONS=$(jq -r '.violations | join("; ")' "$OUTPUT")
  echo "BASELINE_FAIL: ${REASONS}" >&2
  exit 1
fi
