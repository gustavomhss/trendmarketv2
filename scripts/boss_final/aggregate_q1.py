#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Dict, List

BASE_DIR = Path(__file__).resolve().parents[2]
STAGES_DIR = BASE_DIR / "out" / "q1_boss_final" / "stages"
OUTPUT_DIR = BASE_DIR / "out" / "q1_boss_final"
ERROR_PREFIX = "BOSS-E"
STAGES = ["s1", "s2", "s3", "s4", "s5", "s6"]


@dataclass
class StageBundle:
    stage: str
    status: str
    notes: str


def fail(code: str, message: str) -> None:
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)
    (OUTPUT_DIR / "guard_status.txt").write_text("FAIL\n", encoding="utf-8")
    raise SystemExit(f"{ERROR_PREFIX}-{code}:{message}")


def read_text(path: Path, code: str) -> str:
    try:
        return path.read_text(encoding="utf-8")
    except FileNotFoundError:
        fail(code, f"Missing required file: {path}")
    except OSError as exc:
        fail(code, f"Could not read {path}: {exc}")


def load_stage(stage: str) -> StageBundle:
    stage_dir = STAGES_DIR / stage
    if not stage_dir.exists():
        fail("STAGE-DIR", f"Stage directory missing: {stage_dir}")

    stage_path = stage_dir / "stage.json"
    raw = read_text(stage_path, "STAGE-JSON")
    try:
        data = json.loads(raw)
    except json.JSONDecodeError as exc:
        fail("STAGE-JSON", f"Invalid JSON in {stage_path}: {exc}")

    if data.get("stage") != stage:
        fail("STAGE-ID", f"Stage id mismatch for {stage}: {data.get('stage')}")

    status = str(data.get("status", "")).upper()
    notes = str(data.get("notes", "")).strip()
    if status not in {"PASS", "FAIL"}:
        fail("STAGE-STATUS", f"Stage {stage} reported invalid status: {status}")
    if not notes:
        fail("STAGE-NOTES", f"Stage {stage} did not provide notes")

    guard_path = stage_dir / "guard_status.txt"
    guard_status = read_text(guard_path, "STAGE-GUARD").strip().upper()
    if guard_status not in {"PASS", "FAIL"}:
        fail("STAGE-GUARD", f"Invalid guard status for {stage}: {guard_status}")
    if guard_status != status:
        fail("STAGE-DIVERGENCE", f"Stage {stage} mismatch between guard ({guard_status}) and status ({status})")

    return StageBundle(stage=stage, status=status, notes=notes)


def load_all_stages() -> Dict[str, StageBundle]:
    bundles: Dict[str, StageBundle] = {}
    for stage in STAGES:
        bundles[stage] = load_stage(stage)
    return bundles


def compute_bundle_hash(bundles: Dict[str, StageBundle]) -> str:
    canonical = {
        stage: {"status": bundle.status, "notes": bundle.notes}
        for stage, bundle in sorted(bundles.items())
    }
    payload = json.dumps(canonical, ensure_ascii=False, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def build_report(bundles: Dict[str, StageBundle]) -> dict:
    timestamp = datetime.now(timezone.utc).replace(microsecond=0).isoformat()
    overall = "PASS" if all(bundle.status == "PASS" for bundle in bundles.values()) else "FAIL"
    sprints = {stage: {"status": bundle.status, "notes": bundle.notes} for stage, bundle in bundles.items()}
    bundle_hash = compute_bundle_hash(bundles)
    return {
        "schema_version": 1,
        "timestamp_utc": timestamp,
        "status": overall,
        "sprints": sprints,
        "bundle_sha256": bundle_hash,
    }


def render_report_md(report: dict) -> str:
    lines: List[str] = ["# Q1 Boss Final", ""]
    lines.append(f"- Timestamp (UTC): {report['timestamp_utc']}")
    lines.append(f"- Overall status: **{report['status']}**")
    lines.append(f"- Bundle SHA-256: `{report['bundle_sha256']}`")
    lines.append("")
    lines.append("## Stage breakdown")
    lines.append("| Stage | Status | Notes |")
    lines.append("| --- | --- | --- |")
    for stage in STAGES:
        entry = report["sprints"][stage]
        notes = entry["notes"].replace("\n", "<br>")
        lines.append(f"| {stage.upper()} | {entry['status']} | {notes} |")
    return "\n".join(lines) + "\n"


def render_badge(report: dict) -> str:
    status = report["status"]
    color = "#2e8540" if status == "PASS" else "#c92a2a"
    return (
        "<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"200\" height=\"40\">"
        f"<rect width=\"200\" height=\"40\" fill=\"{color}\" rx=\"6\"/>"
        "<text x=\"100\" y=\"25\" text-anchor=\"middle\" fill=\"#ffffff\" font-size=\"18\" "
        "font-family=\"Helvetica,Arial,sans-serif\">Q1 {status}</text>"
        "</svg>"
    )


def render_dag(report: dict) -> str:
    width = 140 * len(STAGES)
    svg = [
        f"<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"{width}\" height=\"120\">",
        "<style>text{font-family:Helvetica,Arial,sans-serif;font-size:14px;}</style>",
        "<defs><marker id=\"arrow\" markerWidth=\"10\" markerHeight=\"7\" refX=\"10\" refY=\"3.5\" orient=\"auto\"><polygon points=\"0 0, 10 3.5, 0 7\" fill=\"#1f2933\"/></marker></defs>",
    ]
    for index, stage in enumerate(STAGES):
        entry = report["sprints"][stage]
        status = entry["status"]
        color = "#2e8540" if status == "PASS" else "#c92a2a"
        x = 70 + index * 140
        svg.append(f"<circle cx=\"{x}\" cy=\"50\" r=\"35\" fill=\"{color}\" />")
        svg.append(f"<text x=\"{x}\" y=\"55\" text-anchor=\"middle\" fill=\"#ffffff\">{stage.upper()}</text>")
        if index < len(STAGES) - 1:
            next_x = 70 + (index + 1) * 140
            svg.append(
                f"<line x1=\"{x + 35}\" y1=\"50\" x2=\"{next_x - 35}\" y2=\"50\" stroke=\"#1f2933\" stroke-width=\"2\" marker-end=\"url(#arrow)\" />"
            )
    svg.append("</svg>")
    return "".join(svg)


def build_pr_comment(report: dict) -> str:
    lines = [f"### Q1 Boss Final — {report['status']}"]
    lines.append("")
    lines.append("| Stage | Status | Notes |")
    lines.append("| --- | --- | --- |")
    for stage in STAGES:
        entry = report["sprints"][stage]
        notes = entry["notes"].replace("\n", "<br>")
        lines.append(f"| {stage.upper()} | {entry['status']} | {notes} |")
    lines.append("")
    lines.append(f"Bundle SHA-256: `{report['bundle_sha256']}`")
    return "\n".join(lines) + "\n"


def write_outputs(report: dict) -> None:
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)
    (OUTPUT_DIR / "report.json").write_text(
        json.dumps(report, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    (OUTPUT_DIR / "report.md").write_text(render_report_md(report), encoding="utf-8")
    (OUTPUT_DIR / "badge.svg").write_text(render_badge(report) + "\n", encoding="utf-8")
    (OUTPUT_DIR / "dag.svg").write_text(render_dag(report) + "\n", encoding="utf-8")
    (OUTPUT_DIR / "pr_comment.md").write_text(build_pr_comment(report), encoding="utf-8")
    (OUTPUT_DIR / "guard_status.txt").write_text(report["status"] + "\n", encoding="utf-8")


def main() -> int:
    bundles = load_all_stages()
    report = build_report(bundles)
    write_outputs(report)
    if report["status"] != "PASS":
        print(f"{ERROR_PREFIX}-AGG-FAIL:One or more stages failed", file=sys.stderr)
        return 1
    print("PASS Q1 Boss Final")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
