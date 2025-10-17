"""Utilities for generating the CRD-8 release manifest and metadata."""

from __future__ import annotations

import json
from datetime import datetime, timezone
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, Optional


class ReleaseManifestError(RuntimeError):
    """Raised when the release manifest preconditions are not met."""


@dataclass(frozen=True)
class _Context:
    out_dir: Path

    @property
    def evidence_dir(self) -> Path:
        return self.out_dir / "evidence"

    @property
    def bundle_path(self) -> Path:
        return self.out_dir / "bundle.zip"

    @property
    def bundle_sha_path(self) -> Path:
        return self.out_dir / "bundle.sha256.txt"

    def evidence_file(self, name: str) -> Path:
        return self.evidence_dir / name


def _load_json(path: Path) -> Dict[str, Any]:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        raise ReleaseManifestError(f"JSON inválido em {path}: {exc}") from exc


def _load_optional_json(path: Path) -> Optional[Dict[str, Any]]:
    if not path.exists():
        return None
    data = _load_json(path)
    return data if data else {}


def _bundle_sha(context: _Context) -> Optional[str]:
    sha_path = context.bundle_sha_path
    if not sha_path.exists():
        return None
    content = sha_path.read_text(encoding="utf-8").strip()
    if not content:
        return None
    return content.split()[0]


def _bundle_metadata(context: _Context) -> Dict[str, Any]:
    metadata: Dict[str, Any] = {
        "path": str(context.bundle_path),
        "sha256": _bundle_sha(context),
        "size_bytes": None,
    }
    if context.bundle_path.exists():
        metadata["size_bytes"] = context.bundle_path.stat().st_size
    return metadata


def _evidence_checks(context: _Context) -> Dict[str, bool]:
    ev = context.evidence_dir
    return {
        "metrics_unit": (ev / "metrics_unit.json").exists(),
        "prometheus_text": (ev / "amm_metrics.prom").exists(),
        "amm_state": (ev / "amm_obs_state.json").exists(),
        "metrics_summary": (ev / "metrics_summary.json").exists(),
        "trace_log_smoke": (ev / "trace_log_smoke.json").exists(),
        "pii_probe": (ev / "pii_probe.json").exists(),
        "synthetic_probe": (ev / "synthetic_probe.json").exists(),
        "chaos_summary": (ev / "chaos_summary.json").exists(),
        "costs_cardinality": (ev / "costs_cardinality.json").exists(),
        "sbom": (ev / "sbom.cdx.json").exists(),
        "baseline_perf": (ev / "baseline_perf.json").exists(),
        "golden_traces": (ev / "golden_traces.json").exists(),
    }


def _sbom_sha(context: _Context) -> Optional[str]:
    sha_file = context.evidence_file("sbom.cdx.sha256")
    if not sha_file.exists():
        return None
    content = sha_file.read_text(encoding="utf-8").strip()
    if not content:
        return None
    return content.split()[0]


def generate_release_manifest(out_dir: Path) -> Dict[str, Any]:
    """Build the release manifest payload for ``out/obs_gatecheck``."""

    context = _Context(out_dir=out_dir)
    summary_path = context.out_dir / "summary.json"
    if not summary_path.exists():
        raise FileNotFoundError(
            "summary.json ausente; execute orr_all.sh antes do manifesto"
        )

    summary = _load_json(summary_path)
    if summary.get("acceptance") != "OK" or summary.get("gatecheck") != "OK":
        raise ReleaseManifestError("SUMMARY_FAIL")

    checks = _evidence_checks(context)

    costs = (
        _load_optional_json(context.evidence_file("costs_cardinality.json"))
        if checks["costs_cardinality"]
        else None
    )
    probe = (
        _load_optional_json(context.evidence_file("synthetic_probe.json"))
        if checks["synthetic_probe"]
        else None
    )
    metrics_summary = (
        _load_optional_json(context.evidence_file("metrics_summary.json"))
        if checks["metrics_summary"]
        else None
    )
    watchers = _load_optional_json(context.evidence_file("watchers_simulation.json"))
    trace_smoke = (
        _load_optional_json(context.evidence_file("trace_log_smoke.json"))
        if checks["trace_log_smoke"]
        else None
    )
    pii_probe = (
        _load_optional_json(context.evidence_file("pii_probe.json"))
        if checks["pii_probe"]
        else None
    )
    chaos_summary = (
        _load_optional_json(context.evidence_file("chaos_summary.json"))
        if checks["chaos_summary"]
        else None
    )
    baseline = (
        _load_optional_json(context.evidence_file("baseline_perf.json"))
        if checks["baseline_perf"]
        else None
    )
    golden_traces = (
        _load_optional_json(context.evidence_file("golden_traces.json"))
        if checks["golden_traces"]
        else None
    )

    manifest = {
        "summary": summary,
        "bundle": _bundle_metadata(context),
        "evidence_checks": checks,
        "costs": (
            {
                "total_estimated_usd_month": costs.get("total_estimated_usd_month"),
                "max_ratio": costs.get("max_ratio"),
                "max_metric": costs.get("max_ratio_metric"),
            }
            if costs is not None
            else None
        ),
        "synthetic_probe": (
            {
                "ok": probe.get("ok"),
                "total": probe.get("total"),
                "ok_ratio": probe.get("ok_ratio"),
            }
            if probe is not None
            else None
        ),
        "metrics": (
            {
                "p95_swap_seconds": metrics_summary.get("p95_swap_seconds"),
                "synthetic_swap_ok_ratio": metrics_summary.get(
                    "synthetic_swap_ok_ratio"
                ),
            }
            if metrics_summary is not None
            else None
        ),
        "watchers": (
            {
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
            else None
        ),
        "drills": {
            key: value
            for key, value in {
                "trace_log_smoke": (
                    {
                        "total_spans": trace_smoke.get("total_spans"),
                        "correlated_ratio": trace_smoke.get("correlated_ratio"),
                        "observability_level": trace_smoke.get(
                            "observability_level"
                        ),
                        "skipped": trace_smoke.get("skipped", False),
                    }
                    if trace_smoke is not None
                    else None
                ),
                "pii_probe": (
                    {
                        "fields": sorted(pii_probe.keys()),
                        "pii_fields": [
                            field
                            for field in pii_probe.keys()
                            if field.lower()
                            in {"cpf", "email", "name", "phone", "document"}
                        ],
                    }
                    if pii_probe is not None
                    else None
                ),
                "chaos": chaos_summary if chaos_summary is not None else None,
                "baseline_perf": baseline if baseline is not None else None,
                "golden_traces": golden_traces if golden_traces is not None else None,
            }.items()
            if value is not None
        },
        "sbom": (
            {
                "path": str(context.evidence_file("sbom.cdx.json")),
                "sha256": _sbom_sha(context),
            }
            if checks["sbom"]
            else None
        ),
    }

    return manifest


def write_release_manifest(out_dir: Path) -> Path:
    """Persist the manifest JSON and return the file path."""

    manifest = generate_release_manifest(out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    manifest_path = out_dir / "release_manifest.json"
    manifest_path.write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    return manifest_path


def _parse_summary_ts(summary: Dict[str, Any]) -> datetime:
    ts = summary.get("ts")
    if not ts:
        raise ReleaseManifestError("SUMMARY_TS_MISSING")
    try:
        if ts.endswith("Z"):
            ts = ts[:-1] + "+00:00"
        return datetime.fromisoformat(ts)
    except ValueError as exc:
        raise ReleaseManifestError(f"SUMMARY_TS_INVALID: {ts}") from exc


def _derive_release_version(summary: Dict[str, Any], override: Optional[str]) -> str:
    if override:
        return override
    return _parse_summary_ts(summary).astimezone(timezone.utc).strftime("%Y%m%d")


def build_release_metadata(out_dir: Path, *, version: Optional[str] = None) -> Dict[str, Any]:
    """Return a consolidated metadata payload derived from the manifest."""

    manifest_path = write_release_manifest(out_dir)
    manifest = _load_json(manifest_path)
    summary = manifest.get("summary", {})

    release_version = _derive_release_version(summary, version)
    tag = f"crd-8-obs-{release_version}"

    metadata: Dict[str, Any] = {
        "tag": tag,
        "version": release_version,
        "manifest_path": str(manifest_path),
        "summary": {
            "ts": summary.get("ts"),
            "profile": summary.get("profile"),
            "environment": summary.get("environment"),
            "acceptance": summary.get("acceptance"),
            "gatecheck": summary.get("gatecheck"),
        },
        "bundle": manifest.get("bundle"),
        "evidence_checks": manifest.get("evidence_checks"),
        "costs": manifest.get("costs"),
        "synthetic_probe": manifest.get("synthetic_probe"),
        "metrics": manifest.get("metrics"),
        "watchers": manifest.get("watchers"),
        "drills": manifest.get("drills"),
        "sbom": manifest.get("sbom"),
    }

    return metadata


def write_release_metadata(out_dir: Path, *, version: Optional[str] = None) -> Path:
    """Persist the release metadata file and return its path."""

    metadata = build_release_metadata(out_dir, version=version)
    out_dir.mkdir(parents=True, exist_ok=True)
    metadata_path = out_dir / "release_metadata.json"
    metadata_path.write_text(json.dumps(metadata, indent=2) + "\n", encoding="utf-8")
    return metadata_path


__all__ = [
    "ReleaseManifestError",
    "generate_release_manifest",
    "write_release_manifest",
    "build_release_metadata",
    "write_release_metadata",
]
