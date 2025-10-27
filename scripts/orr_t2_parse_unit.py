#!/usr/bin/env python3
import json
import os
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "src"
if str(SRC) not in sys.path:
    sys.path.insert(0, str(SRC))

from amm_obs import AMMObservability  # noqa: E402

EVIDENCE = ROOT / "out" / "obs_gatecheck" / "evidence"
EVIDENCE.mkdir(parents=True, exist_ok=True)

obs = AMMObservability(
    env=os.getenv("OBS_ENV", "dev"),
    service=os.getenv("OBS_SERVICE", "trendmarket-amm"),
    version=os.getenv("OBS_VERSION", "v0.1.0"),
    observability_level=os.getenv("OBSERVABILITY_LEVEL", "full"),
)
obs.simulate_unit_load()
obs.write_metrics_unit(EVIDENCE / "metrics_unit.json")
obs.write_prometheus_file(EVIDENCE / "amm_metrics.prom")
obs.write_state(EVIDENCE / "amm_obs_state.json")

# Generate a lightweight summary for humans skimming the bundle.
summary_path = EVIDENCE / "metrics_summary.json"
snapshot = obs.metrics_snapshot()
sample_swap = snapshot["operations"].get("swap", {})
supporting = snapshot.get("supporting", {})
synthetic = supporting.get("synthetic", {})
synthetic_swap = synthetic.get("swap", {})


def _find_value(points, **expected_labels):
    for point in points:
        labels = point.get("labels", {})
        if all(labels.get(key) == value for key, value in expected_labels.items()):
            return point.get("value")
    return None


summary = {
    "p95_swap_seconds": sample_swap.get("p95"),
    "count_swap": sample_swap.get("count"),
    "exemplar_trace_id": snapshot["exemplars"].get("swap", {}).get("trace_id"),
    "freshness_oracle_seconds": _find_value(
        supporting.get("data_freshness_seconds", []), source="oracle"
    ),
    "cdc_orders_partition0_seconds": _find_value(
        supporting.get("cdc_lag_seconds", []), stream="orders", partition="0"
    ),
    "hook_coverage_ratio": supporting.get("hook_coverage_ratio", {}).get("value"),
    "synthetic_swap_ok_ratio": synthetic_swap.get("ok_ratio"),
    "synthetic_swap_count": synthetic_swap.get("count"),
}
cardinality = snapshot.get("cardinality", {})
summary.update(
    {
        "total_estimated_cost_usd_month": cardinality.get("total_estimated_usd_month"),
        "max_cardinality_ratio": cardinality.get("max_ratio"),
        "max_cardinality_metric": cardinality.get("max_ratio_metric"),
    }
)
summary_path.write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")

# Enforce label contract.
subprocess.run(
    [sys.executable, str(ROOT / "scripts" / "prom_label_lint.py")], check=True, cwd=ROOT
)
print("T2_OK")
