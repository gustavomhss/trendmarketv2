#!/usr/bin/env bash
set -euo pipefail

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
