#!/usr/bin/env python3
import json
import re
import sys
from pathlib import Path


def main() -> int:
    evidence_dir = Path("out/obs_gatecheck/evidence")
    evidence_dir.mkdir(parents=True, exist_ok=True)

    allow = {
        "amm_op_latency_seconds": {"op", "env", "service", "version"},
        "data_freshness_seconds": {"env", "service", "version"},
        "cdc_lag_seconds": {"env", "service", "version"},
        "drift_score": {"env", "service", "version"},
        "hook_coverage_ratio": {"env", "service", "version"},
        "hook_execution_seconds": {"op", "env", "service", "version"},
    }

    violations = []
    metric_pattern = re.compile(
        r"(amm_op_latency_seconds|data_freshness_seconds|cdc_lag_seconds|drift_score|hook_coverage_ratio|hook_execution_seconds)\{([^}]*)\}"
    )

    candidates = []
    for pattern in ("*.yml", "*.yaml", "*.prom", "*.tmpl"):
        candidates.extend(Path(".").rglob(pattern))

    for path in candidates:
        try:
            txt = path.read_text(errors="ignore")
        except Exception:
            continue
        for match in metric_pattern.finditer(txt):
            name = match.group(1)
            labels = match.group(2)
            keys = {kv.split("=")[0].strip() for kv in labels.split(",") if "=" in kv}
            if not keys.issubset(allow.get(name, set())):
                violations.append(
                    {"file": str(path), "metric": name, "labels": sorted(keys)}
                )

    (evidence_dir / "label_lint.json").write_text(
        json.dumps({"violations": violations}, indent=2)
    )
    if violations:
        print("LABELS_FAIL")
        return 1
    print("LABELS_OK")
    return 0


if __name__ == "__main__":
    sys.exit(main())
