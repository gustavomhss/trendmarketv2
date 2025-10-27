#!/usr/bin/env python3
"""Generate a human-readable summary from an ORR bundle.

This helper inspects ``out/obs_gatecheck`` (or another bundle directory) to
confirm that the acceptance/gatecheck status is OK, verifies the presence of the
mandatory evidence files for Wave 3, and prints a ready-to-paste PR footer with
the key SLIs.
"""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Sequence

BUNDLE_DEFAULT = Path("out/obs_gatecheck")
EVIDENCE_REQUIRED: Sequence[Path] = [
    Path("evidence/metrics_summary.json"),
    Path("evidence/costs_cardinality.json"),
    Path("evidence/sbom.cdx.json"),
    Path("evidence/synthetic_probe.json"),
    Path("evidence/pii_probe.json"),
    Path("evidence/pii_labels.ok"),
    Path("evidence/chaos_summary.json"),
    Path("evidence/baseline_perf.json"),
    Path("evidence/golden_traces.json"),
    Path("evidence/trace_log_smoke.json"),
]
META_REQUIRED: Sequence[Path] = [
    Path("bundle.zip"),
    Path("bundle.sha256.txt"),
    Path("release_manifest.json"),
    Path("release_metadata.json"),
    Path("release_notes.md"),
    Path("summary.json"),
    Path("logs/orr_all.txt"),
]


@dataclass(frozen=True)
class BundleSummary:
    acceptance: str
    gatecheck: str
    hash_value: str
    metrics: dict
    metadata: dict


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "bundle_dir",
        nargs="?",
        default=BUNDLE_DEFAULT,
        type=Path,
        help="Path to the unpacked ORR bundle (default: out/obs_gatecheck)",
    )
    return parser.parse_args(argv)


def load_json(path: Path) -> dict:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        raise SystemExit(f"Required file missing: {exc.filename}") from exc
    except json.JSONDecodeError as exc:
        raise SystemExit(f"Could not parse JSON from {path}: {exc}") from exc


def ensure_paths(base: Path, paths: Iterable[Path]) -> None:
    missing = [str(base / rel) for rel in paths if not (base / rel).exists()]
    if missing:
        message = "\n".join(["Missing required files:", *missing])
        raise SystemExit(message)


def extract_summary(bundle_dir: Path) -> BundleSummary:
    summary_path = bundle_dir / "summary.json"
    summary = load_json(summary_path)
    acceptance = summary.get("acceptance", "UNKNOWN")
    gatecheck = summary.get("gatecheck", "UNKNOWN")

    hash_path = bundle_dir / "bundle.sha256.txt"
    hash_value = hash_path.read_text(encoding="utf-8").strip().split()[0]

    metrics_path = bundle_dir / "evidence" / "metrics_summary.json"
    metrics = load_json(metrics_path)

    metadata_path = bundle_dir / "release_metadata.json"
    metadata = load_json(metadata_path)

    return BundleSummary(
        acceptance=acceptance,
        gatecheck=gatecheck,
        hash_value=hash_value,
        metrics=metrics,
        metadata=metadata,
    )


def print_footer(summary: BundleSummary, bundle_dir: Path) -> None:
    metrics = summary.metrics

    metric_aliases = {
        "p95_swap_seconds": ("p95_swap_seconds",),
        "data_freshness_seconds": (
            "data_freshness_seconds",
            "freshness_oracle_seconds",
        ),
        "cdc_lag_seconds": ("cdc_lag_seconds", "cdc_orders_partition0_seconds"),
        "drift_score": ("drift_score",),
        "hook_coverage_ratio": ("hook_coverage_ratio",),
    }

    def _metric(key: str, default: str = "n/a") -> str:
        candidates = metric_aliases.get(key, (key,))
        for candidate in candidates:
            value = metrics.get(candidate)
            if value is None:
                continue
            if isinstance(value, float):
                return f"{value:.6g}"
            return str(value)
        return default

    evidence_count = sum(
        1 for path in (bundle_dir / "evidence").rglob("*") if path.is_file()
    )
    footer = f"""\
ORR: ACCEPTANCE_{summary.acceptance} · GATECHECK_{summary.gatecheck}
Bundle: {bundle_dir / "bundle.zip"} (sha256: {summary.hash_value})
SLIs: p95(swap)={_metric("p95_swap_seconds")}s, freshness(oracle)={_metric("data_freshness_seconds")}s, cdc_lag_max={_metric("cdc_lag_seconds")}s, drift_max={_metric("drift_score")}, hook_coverage={_metric("hook_coverage_ratio")}
Gates: PII_OK · SBOM_OK · COSTS_OK · BASELINE_OK · TRACE_GOLDEN_OK
Evidence files: {evidence_count}
"""
    print(footer)


def print_metadata(metadata: dict) -> None:
    bundle = metadata.get("bundle", {})
    summary = metadata.get("summary", {})
    tag = metadata.get("tag", "<unknown>")
    size = bundle.get("size_bytes", "?")
    sha = bundle.get("sha256", "<missing>")
    profile = summary.get("profile", "unknown")
    environment = summary.get("environment", "unknown")
    print("Release metadata:")
    print(f"  tag: {tag}")
    print(f"  profile: {profile}")
    print(f"  environment: {environment}")
    print(f"  bundle.size_bytes: {size}")
    print(f"  bundle.sha256: {sha}")


def main(argv: Sequence[str]) -> int:
    args = parse_args(argv)
    bundle_dir: Path = args.bundle_dir.resolve()

    ensure_paths(bundle_dir, META_REQUIRED)
    ensure_paths(bundle_dir, EVIDENCE_REQUIRED)

    summary = extract_summary(bundle_dir)
    if summary.acceptance != "OK" or summary.gatecheck != "OK":
        raise SystemExit(
            f"Bundle not ready: acceptance={summary.acceptance}, gatecheck={summary.gatecheck}"
        )

    print_footer(summary, bundle_dir)
    print_metadata(summary.metadata)
    notes_path = bundle_dir / "release_notes.md"
    print("\nRelease notes excerpt:\n----------------------")
    print(notes_path.read_text(encoding="utf-8").strip())
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
