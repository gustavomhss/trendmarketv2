"""Assemble deterministic ORR evidence bundle for Sprint 7."""

from __future__ import annotations

import argparse
import json
import os
import subprocess
from datetime import datetime, timezone
from pathlib import Path
from typing import Sequence
from zipfile import ZIP_DEFLATED, ZipFile, ZipInfo

DEFAULT_SUMMARY = "out/orr_s7/RESUMO_ORR_S7.json"
DEFAULT_BUNDLE = "out/s7-orr-evidence.zip"
DEFAULT_FILELIST = "out/orr_s7/filelist.txt"

GITLEAKS_SUMMARY = "out/evidence/T2_security/gitleaks_summary.json"
YAMLLINT_SUMMARY = "out/evidence/T1_yaml/yamllint_summary.json"
TESTS_SUMMARY = "out/evidence/T4_tests/pytest_summary.json"
CI_SUMMARY = "out/evidence/T0_ci/render_summary.json"

WATCHERS_BASELINE = {
    "data_freshness_seconds": 0,
    "drift_score": 0,
    "failover_time_p95_s": 0,
}


def load_json(path: Path) -> dict[str, object]:
    if not path.exists():
        return {"status": "MISSING", "path": path.as_posix()}
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        return {"status": "INVALID_JSON", "path": path.as_posix()}


def discover_versions() -> dict[str, str]:
    versions: dict[str, str] = {}
    commands = {
        "python": ["python", "--version"],
        "jq": ["jq", "--version"],
        "yamllint": ["yamllint", "--version"],
        "gitleaks": ["gitleaks", "version"],
    }
    for tool, cmd in commands.items():
        try:
            output = subprocess.check_output(cmd, text=True, stderr=subprocess.STDOUT)
        except (FileNotFoundError, subprocess.CalledProcessError):
            versions[tool] = "[skip]"
        else:
            versions[tool] = output.strip()
    return versions


def build_summary(
    summary_path: Path,
    t0_payload: Path,
    evidence_paths: Sequence[Path],
) -> dict[str, object]:
    summary: dict[str, object] = {
        "gate": "S7_EXEC",
        "timestamp_utc": datetime.now(timezone.utc).isoformat(),
        "commit": os.getenv("GITHUB_SHA", "unknown"),
        "branch": os.getenv("GITHUB_REF", "unknown"),
        "watchers": WATCHERS_BASELINE,
        "versions": discover_versions(),
    }
    t0_data = load_json(t0_payload)
    summary["t0_spec"] = t0_data
    gates = {
        "ci_render": load_json(Path(CI_SUMMARY)),
        "yamllint": load_json(Path(YAMLLINT_SUMMARY)),
        "gitleaks": load_json(Path(GITLEAKS_SUMMARY)),
        "tests": load_json(Path(TESTS_SUMMARY)),
    }
    summary["gates"] = gates
    verdict = "PASS"
    for key, gate in gates.items():
        status = str(gate.get("status", "UNKNOWN")).upper()
        if key in {"yamllint", "tests"} and status not in {"PASS", "SKIP"}:
            verdict = "FAIL"
    if str(t0_data.get("status")).upper() != "PASS":
        verdict = "FAIL"
    summary["verdict"] = verdict
    summary_path.parent.mkdir(parents=True, exist_ok=True)
    summary_path.write_text(
        json.dumps(summary, ensure_ascii=False, sort_keys=True, indent=2),
        encoding="utf-8",
    )
    return summary


def deterministic_zip(bundle_path: Path, files: Sequence[Path]) -> None:
    bundle_path.parent.mkdir(parents=True, exist_ok=True)
    with ZipFile(bundle_path, "w", compression=ZIP_DEFLATED, compresslevel=6) as zf:
        for path in sorted(files, key=lambda item: item.as_posix()):
            info = ZipInfo.from_file(path, arcname=path.as_posix())
            info.date_time = (1970, 1, 1, 0, 0, 0)
            info.create_system = 3
            with path.open("rb") as handle:
                zf.writestr(info, handle.read())


def write_filelist(filelist_path: Path, files: Sequence[Path]) -> None:
    filelist_path.parent.mkdir(parents=True, exist_ok=True)
    with filelist_path.open("w", encoding="utf-8", newline="\n") as handle:
        for path in sorted(files, key=lambda item: item.as_posix()):
            handle.write(f"{path.as_posix()}\n")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Bundle Sprint 7 evidence")
    parser.add_argument("--summary", default=DEFAULT_SUMMARY)
    parser.add_argument("--bundle", default=DEFAULT_BUNDLE)
    parser.add_argument("--filelist", default=DEFAULT_FILELIST)
    parser.add_argument("--t0", default="out/obs_gatecheck/T0_discovery.json")
    parser.add_argument(
        "--include",
        nargs="*",
        default=[
            CI_SUMMARY,
            YAMLLINT_SUMMARY,
            GITLEAKS_SUMMARY,
            TESTS_SUMMARY,
        ],
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    include_paths = [Path(item) for item in args.include]
    t0_path = Path(args.t0)
    summary_path = Path(args.summary)
    bundle_path = Path(args.bundle)
    filelist_path = Path(args.filelist)

    summary = build_summary(summary_path, t0_path, include_paths)
    files_for_zip = [summary_path] + include_paths
    deterministic_zip(bundle_path, [path for path in files_for_zip if path.exists()])
    write_filelist(filelist_path, [summary_path, *include_paths])
    return 0 if summary.get("verdict") == "PASS" else 1


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
