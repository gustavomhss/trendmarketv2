#!/usr/bin/env python3
"""Aggregate Boss Final stage results for Q1."""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Dict, List, Sequence

BASE_DIR = Path(__file__).resolve().parents[2]
STAGES = ("s1", "s2", "s3", "s4", "s5", "s6")
OUTPUT_DIR = BASE_DIR / "out" / "q1_boss_final"
STAGES_DIR = OUTPUT_DIR / "stages"
SCHEMA_VERSION = 1
ERROR_PREFIX = "BOSS-E"


@dataclass(frozen=True)
class StageSummary:
    stage: str
    status: str
    notes: str
    variants: Dict[str, Dict[str, object]]


@dataclass(frozen=True)
class AggregateArtifacts:
    report: Dict[str, object]
    stage_summaries: Dict[str, StageSummary]
    bundle_sha256: str


def isoformat_utc() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def canonical_dumps(payload: Dict[str, object]) -> str:
    return json.dumps(payload, sort_keys=True, ensure_ascii=False, separators=(",", ":")) + "\n"


def load_json(path: Path) -> Dict[str, object]:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        raise RuntimeError(f"{ERROR_PREFIX}-E-MISSING: {path} ausente") from exc


def load_stage_variant(stage: str, variant: str) -> Dict[str, object]:
    directory = STAGES_DIR / stage / variant
    result_path = directory / "result.json"
    if not result_path.exists():
        raise RuntimeError(f"{ERROR_PREFIX}-E-RESULT: resultado ausente para {stage}/{variant}")
    result = load_json(result_path)
    guard_path = directory / "guard_status.txt"
    guard = guard_path.read_text(encoding="utf-8").strip() if guard_path.exists() else "MISSING"
    result.setdefault("guard_status", guard)
    return result


def summarise_stage(stage: str) -> StageSummary:
    variants: Dict[str, Dict[str, object]] = {}
    statuses: List[str] = []
    notes_parts: List[str] = []
    for variant in ("primary", "clean"):
        variant_result = load_stage_variant(stage, variant)
        variants[variant] = variant_result
        status = variant_result.get("status", "FAIL").upper()
        statuses.append(status)
        variant_note = variant_result.get("notes", "")
        notes_parts.append(f"{variant}:{status}{(' ' + variant_note) if variant_note else ''}")
    stage_status = "PASS" if all(status == "PASS" for status in statuses) else "FAIL"
    notes = " | ".join(notes_parts)
    return StageSummary(stage=stage, status=stage_status, notes=notes, variants=variants)


def compute_bundle_sha(stage_summaries: Dict[str, StageSummary]) -> str:
    pieces: List[str] = []
    for stage in STAGES:
        summary = stage_summaries[stage]
        for variant in ("primary", "clean"):
            variant_payload = summary.variants[variant]
            pieces.append(canonical_dumps({
                "stage": stage,
                "variant": variant,
                "status": variant_payload.get("status"),
                "notes": variant_payload.get("notes"),
                "timestamp_utc": variant_payload.get("timestamp_utc"),
            }))
    concatenated = "".join(pieces)
    return hashlib.sha256(concatenated.encode("utf-8")).hexdigest()


def build_report(stage_summaries: Dict[str, StageSummary], bundle_sha: str, release_tag: str | None) -> Dict[str, object]:
    report = {
        "schema": "trendmarketv2.q1.boss.report",
        "schema_version": SCHEMA_VERSION,
        "timestamp_utc": isoformat_utc(),
        "status": "PASS" if all(summary.status == "PASS" for summary in stage_summaries.values()) else "FAIL",
        "sprints": {
            stage: {
                "status": summary.status,
                "notes": summary.notes,
            }
            for stage, summary in stage_summaries.items()
        },
        "bundle": {"sha256": bundle_sha},
    }
    if release_tag:
        report["release_tag"] = release_tag
    return report


def render_markdown(artifacts: AggregateArtifacts) -> str:
    lines = ["# Q1 Boss Final", ""]
    emoji = "✅" if artifacts.report["status"] == "PASS" else "❌"
    lines.append(f"{emoji} Status global: **{artifacts.report['status']}**")
    lines.append("")
    lines.append(f"- Relatório gerado em: {artifacts.report['timestamp_utc']}")
    if "release_tag" in artifacts.report:
        lines.append(f"- Release tag: {artifacts.report['release_tag']}")
    lines.append(f"- Bundle SHA-256: `{artifacts.bundle_sha256}`")
    lines.append("")
    lines.append("| Stage | Status | Notas |")
    lines.append("| --- | --- | --- |")
    for stage in STAGES:
        summary = artifacts.stage_summaries[stage]
        stage_emoji = "✅" if summary.status == "PASS" else "❌"
        lines.append(f"| {stage.upper()} | {stage_emoji} {summary.status} | {summary.notes} |")
    lines.append("")
    lines.append("## Governança")
    lines.append("- Cada estágio deve publicar bundles para `primary` e `clean`.")
    lines.append("- O status global é FAIL se qualquer estágio falhar em qualquer variante.")
    lines.append("")
    return "\n".join(lines) + "\n"


def render_pr_comment(artifacts: AggregateArtifacts) -> str:
    emoji = "✅" if artifacts.report["status"] == "PASS" else "❌"
    lines = [f"{emoji} [Q1 Boss Final report](./report.md)", ""]
    lines.append("![Status](./badge.svg)")
    lines.append("")
    for stage in STAGES:
        summary = artifacts.stage_summaries[stage]
        stage_emoji = "✅" if summary.status == "PASS" else "❌"
        lines.append(f"- {stage.upper()}: {stage_emoji} {summary.status} — {summary.notes}")
    lines.append("")
    lines.append(f"Bundle SHA-256: `{artifacts.bundle_sha256}`")
    lines.append("")
    lines.append("Relatório completo disponível em [report.md](./report.md).")
    return "\n".join(lines) + "\n"


def render_badge(status: str) -> str:
    color = "4c9a2a" if status == "PASS" else "cc3300"
    return (
        "<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"160\" height=\"20\" role=\"img\">"
        "<linearGradient id=\"b\" x2=\"0\" y2=\"100%\"><stop offset=\"0\" stop-color=\"#bbb\" stop-opacity=\".1\"/>"
        "<stop offset=\"1\" stop-opacity=\".1\"/></linearGradient>"
        "<mask id=\"a\"><rect width=\"160\" height=\"20\" rx=\"3\" fill=\"#fff\"/></mask>"
        "<g mask=\"url(#a)\">"
        "<rect width=\"80\" height=\"20\" fill=\"#555\"/>"
        f"<rect x=\"80\" width=\"80\" height=\"20\" fill=\"#{color}\"/>"
        "<rect width=\"160\" height=\"20\" fill=\"url(#b)\"/></g>"
        "<g fill=\"#fff\" text-anchor=\"middle\" font-family=\"DejaVu Sans,Verdana,Geneva,sans-serif\" font-size=\"11\">"
        "<text x=\"40\" y=\"15\">Q1 Boss</text>"
        f"<text x=\"120\" y=\"15\">{status}</text>"
        "</g></svg>"
    )


def render_dag(stage_summaries: Dict[str, StageSummary], status: str) -> str:
    height = 40 + len(STAGES) * 25
    nodes = []
    for index, stage in enumerate(STAGES):
        summary = stage_summaries[stage]
        y = 40 + index * 25
        color = "#4c9a2a" if summary.status == "PASS" else "#cc3300"
        nodes.append(
            f"<rect x=\"20\" y=\"{y}\" width=\"120\" height=\"20\" rx=\"4\" fill=\"{color}\"/>"
            f"<text x=\"80\" y=\"{y + 15}\" fill=\"#fff\" font-size=\"12\" text-anchor=\"middle\">{stage.upper()} — {summary.status}</text>"
        )
    connector = "".join(nodes)
    header_color = "#4c9a2a" if status == "PASS" else "#cc3300"
    return (
        "<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"320\" height=\"" + str(height) + "\">"
        f"<rect width=\"320\" height=\"30\" fill=\"{header_color}\" rx=\"4\"/>"
        "<text x=\"20\" y=\"20\" font-size=\"16\" fill=\"#fff\">Q1 Boss Final</text>"
        f"{connector}</svg>"
    )


def ensure_output_dir() -> None:
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)


def write_outputs(artifacts: AggregateArtifacts) -> None:
    ensure_output_dir()
    (OUTPUT_DIR / "report.json").write_text(json.dumps(artifacts.report, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    (OUTPUT_DIR / "report.md").write_text(render_markdown(artifacts), encoding="utf-8")
    (OUTPUT_DIR / "badge.svg").write_text(render_badge(artifacts.report["status"]), encoding="utf-8")
    (OUTPUT_DIR / "dag.svg").write_text(render_dag(artifacts.stage_summaries, artifacts.report["status"]), encoding="utf-8")
    (OUTPUT_DIR / "pr_comment.md").write_text(render_pr_comment(artifacts), encoding="utf-8")
    (OUTPUT_DIR / "bundle.sha256").write_text(artifacts.bundle_sha256 + "\n", encoding="utf-8")
    (OUTPUT_DIR / "guard_status.txt").write_text(f"{artifacts.report['status']}\n", encoding="utf-8")


def aggregate(release_tag: str | None = None) -> AggregateArtifacts:
    stage_summaries: Dict[str, StageSummary] = {}
    for stage in STAGES:
        stage_summaries[stage] = summarise_stage(stage)
    bundle_sha = compute_bundle_sha(stage_summaries)
    report = build_report(stage_summaries, bundle_sha, release_tag)
    artifacts = AggregateArtifacts(report=report, stage_summaries=stage_summaries, bundle_sha256=bundle_sha)
    write_outputs(artifacts)
    if artifacts.report["status"] != "PASS":
        raise SystemExit(1)
    return artifacts


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Aggregate Q1 Boss Final stages")
    parser.add_argument("--release-tag", default=None)
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv or sys.argv[1:])
    aggregate(args.release_tag or None)
    return 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main(sys.argv[1:]))
