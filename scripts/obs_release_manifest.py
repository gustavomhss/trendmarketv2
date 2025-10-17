#!/usr/bin/env python3
"""Generate a consolidated manifest for the CRD-8 release bundle."""

import json
import sys
from pathlib import Path
from typing import Any, Dict, Optional
from typing import Optional


ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "out" / "obs_gatecheck"
EVIDENCE = OUT / "evidence"


def _load_json(path: Path) -> Dict[str, Any]:
    if not path.exists():
        return {}
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        raise SystemExit(f"JSON inválido em {path}: {exc}") from exc
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


def _bundle_metadata() -> Dict[str, Any]:
    bundle_path = OUT / "bundle.zip"
    metadata: Dict[str, Any] = {
        "path": str(bundle_path),
        "sha256": _bundle_sha(),
    }
    if bundle_path.exists():
        metadata["size_bytes"] = bundle_path.stat().st_size
    else:
        metadata["size_bytes"] = None
    return metadata


def _optional_payload(filename: str) -> Optional[Dict[str, Any]]:
    path = EVIDENCE / filename
    if not path.exists():
        return None
    data = _load_json(path)
    return data if data else {}


def _sbom_sha() -> Optional[str]:
    sha_file = EVIDENCE / "sbom.cdx.sha256"
    if not sha_file.exists():
        return None
    content = sha_file.read_text(encoding="utf-8").strip()
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

    costs = _optional_payload("costs_cardinality.json") if checks["costs_cardinality"] else None
    probe = _optional_payload("synthetic_probe.json") if checks["synthetic_probe"] else None
    metrics_summary = _optional_payload("metrics_summary.json") if checks["metrics_summary"] else None
    watchers = _optional_payload("watchers_simulation.json")
    trace_smoke = _optional_payload("trace_log_smoke.json")
    pii_probe = _optional_payload("pii_probe.json")
    chaos_summary = _optional_payload("chaos_summary.json")
    baseline = _optional_payload("baseline_perf.json")
    golden_traces = _optional_payload("golden_traces.json")

    manifest = {
        "summary": summary,
        "bundle": _bundle_metadata(),
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
        if costs is not None
        if costs
        else None,
        "synthetic_probe": {
            "ok": probe.get("ok"),
            "total": probe.get("total"),
            "ok_ratio": probe.get("ok_ratio"),
        }
        if probe is not None
        if probe
        else None,
        "metrics": {
            "p95_swap_seconds": metrics_summary.get("p95_swap_seconds"),
            "synthetic_swap_ok_ratio": metrics_summary.get("synthetic_swap_ok_ratio"),
        }
        if metrics_summary is not None
        else None,
        "watchers": {
            "simulated": bool(watchers.get("simulated")),
            "alerts_expected": [
                {
                    "alert": item.get("alert"),
                    "reason": item.get("reason"),
                }
                for item in watchers.get("alerts_expected", [])
            ],
            "alerts_count": len(watchers.get("alerts_expected", [])),
        }
        if watchers is not None
        else None,
        "drills": {
            key: value
            for key, value in {
                "trace_log_smoke": {
                    "total_spans": trace_smoke.get("total_spans"),
                    "correlated_ratio": trace_smoke.get("correlated_ratio"),
                    "observability_level": trace_smoke.get("observability_level"),
                    "skipped": trace_smoke.get("skipped", False),
                }
                if trace_smoke is not None
                else None,
                "pii_probe": {
                    "fields": sorted(pii_probe.keys()),
                    "pii_fields": [
                        field
                        for field in pii_probe.keys()
                        if field.lower() in {"cpf", "email", "name", "phone", "document"}
                    ],
                }
                if pii_probe is not None
                else None,
                "chaos": chaos_summary if chaos_summary is not None else None,
                "baseline_perf": baseline if baseline is not None else None,
                "golden_traces": golden_traces if golden_traces is not None else None,
            }.items()
            if value is not None
        },
        "sbom": {
            "path": str(EVIDENCE / "sbom.cdx.json"),
            "sha256": _sbom_sha(),
        }
        if checks["sbom"]
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
