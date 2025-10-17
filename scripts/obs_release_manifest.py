#!/usr/bin/env python3
"""Generate a consolidated manifest for the CRD-8 release bundle."""

import json
import sys
from pathlib import Path
from typing import Optional


ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "out" / "obs_gatecheck"
EVIDENCE = OUT / "evidence"


def _load_json(path: Path) -> dict:
    if not path.exists():
        return {}
    return json.loads(path.read_text(encoding="utf-8"))


def _bundle_sha() -> Optional[str]:
    sha_path = OUT / "bundle.sha256.txt"
    if not sha_path.exists():
        return None
    content = sha_path.read_text(encoding="utf-8").strip()
    if not content:
        return None
    return content.split()[0]


def main() -> int:
    summary_path = OUT / "summary.json"
    if not summary_path.exists():
        sys.exit("summary.json ausente; execute orr_all.sh antes do manifesto")
    summary = _load_json(summary_path)
    if summary.get("acceptance") != "OK" or summary.get("gatecheck") != "OK":
        sys.exit("SUMMARY_FAIL")

    checks = {
        "metrics_unit": (EVIDENCE / "metrics_unit.json").exists(),
        "prometheus_text": (EVIDENCE / "amm_metrics.prom").exists(),
        "amm_state": (EVIDENCE / "amm_obs_state.json").exists(),
        "metrics_summary": (EVIDENCE / "metrics_summary.json").exists(),
        "trace_log_smoke": (EVIDENCE / "trace_log_smoke.json").exists(),
        "pii_probe": (EVIDENCE / "pii_probe.json").exists(),
        "synthetic_probe": (EVIDENCE / "synthetic_probe.json").exists(),
        "chaos_summary": (EVIDENCE / "chaos_summary.json").exists(),
        "costs_cardinality": (EVIDENCE / "costs_cardinality.json").exists(),
        "sbom": (EVIDENCE / "sbom.cdx.json").exists(),
        "baseline_perf": (EVIDENCE / "baseline_perf.json").exists(),
        "golden_traces": (EVIDENCE / "golden_traces.json").exists(),
    }

    costs = _load_json(EVIDENCE / "costs_cardinality.json") if checks["costs_cardinality"] else {}
    probe = _load_json(EVIDENCE / "synthetic_probe.json") if checks["synthetic_probe"] else {}
    metrics_summary = _load_json(EVIDENCE / "metrics_summary.json") if checks["metrics_summary"] else {}

    manifest = {
        "summary": summary,
        "bundle": {
            "path": str(OUT / "bundle.zip"),
            "sha256": _bundle_sha(),
        },
        "evidence_checks": checks,
        "costs": {
            "total_estimated_usd_month": costs.get("total_estimated_usd_month"),
            "max_ratio": costs.get("max_ratio"),
            "max_metric": costs.get("max_ratio_metric"),
        }
        if costs
        else None,
        "synthetic_probe": {
            "ok": probe.get("ok"),
            "total": probe.get("total"),
            "ok_ratio": probe.get("ok_ratio"),
        }
        if probe
        else None,
        "metrics": {
            "p95_swap_seconds": metrics_summary.get("p95_swap_seconds"),
            "synthetic_swap_ok_ratio": metrics_summary.get("synthetic_swap_ok_ratio"),
        }
        if metrics_summary
        else None,
    }

    OUT.mkdir(parents=True, exist_ok=True)
    manifest_path = OUT / "release_manifest.json"
    manifest_path.write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    print("RELEASE_MANIFEST_OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
