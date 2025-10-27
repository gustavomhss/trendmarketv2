#!/usr/bin/env python3
"""Aggregate Sprint guard outputs into the Q1 Boss Final bundle."""

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
if str(BASE_DIR) not in sys.path:
    sys.path.insert(0, str(BASE_DIR))

import jsonschema  # noqa: E402
STAGES_DIR = BASE_DIR / "out" / "q1_boss_final" / "stages"
OUTPUT_DIR = BASE_DIR / "out" / "q1_boss_final"
SCHEMA_PATH = BASE_DIR / "schemas" / "q1_boss_report.schema.json"
STAGES = ("s1", "s2", "s3", "s4", "s5", "s6")
VARIANTS = ("primary", "clean")
SCHEMA_VERSION = 2


@dataclass(frozen=True)
class VariantResult:
    status: str
    notes: str
    timestamp: str


@dataclass(frozen=True)
class StageAggregate:
    status: str
    notes: str
    variants: Dict[str, VariantResult]


@dataclass(frozen=True)
class AggregateArtifacts:
    report: Dict[str, object]

    def __getitem__(self, key: str) -> object:
        return self.report[key]

    def __iter__(self):  # type: ignore[override]
        return iter(self.report)

    def items(self):
        return self.report.items()


def isoformat_utc() -> str:
    return (
        datetime.now(timezone.utc)
        .replace(microsecond=0)
        .isoformat()
        .replace("+00:00", "Z")
    )


def canonical_dumps(payload: Dict[str, object]) -> str:
    return json.dumps(
        payload, sort_keys=True, ensure_ascii=False, separators=(",", ":")
    )


def load_variant(stage: str, variant: str) -> VariantResult:
    variant_dir = STAGES_DIR / stage / variant
    result_path = variant_dir / "result.json"
    guard_path = variant_dir / "guard_status.txt"
    if not result_path.exists():
        raise RuntimeError(f"{stage}/{variant}: result.json ausente")
    if not guard_path.exists():
        raise RuntimeError(f"{stage}/{variant}: guard_status.txt ausente")
    payload = json.loads(result_path.read_text(encoding="utf-8"))
    status = str(payload.get("status", "FAIL")).upper()
    guard_status = guard_path.read_text(encoding="utf-8").strip().upper()
    if guard_status != status:
        raise RuntimeError(
            f"{stage}/{variant}: divergência entre result.json ({status}) e guard_status ({guard_status})"
        )
    return VariantResult(
        status=status,
        notes=str(payload.get("notes", "")),
        timestamp=str(payload.get("timestamp_utc", "")),
    )


def load_stage_summary(stage: str) -> StageAggregate:
    summary_path = STAGES_DIR / stage / "summary.json"
    guard_path = STAGES_DIR / stage / "guard_status.txt"
    if not summary_path.exists():
        raise RuntimeError(f"{stage}: summary.json ausente")
    if not guard_path.exists():
        raise RuntimeError(f"{stage}: guard_status.txt ausente")
    payload = json.loads(summary_path.read_text(encoding="utf-8"))
    status = str(payload.get("status", "FAIL")).upper()
    guard_status = guard_path.read_text(encoding="utf-8").strip().upper()
    if guard_status != status:
        raise RuntimeError(
            f"{stage}: divergência entre summary.json ({status}) e guard_status ({guard_status})"
        )
    variants: Dict[str, VariantResult] = {}
    for variant in VARIANTS:
        variants[variant] = load_variant(stage, variant)
    return StageAggregate(
        status=status, notes=str(payload.get("notes", "")), variants=variants
    )


def collect_stages() -> Dict[str, StageAggregate]:
    return {stage: load_stage_summary(stage) for stage in STAGES}


def compute_bundle_sha(stages: Dict[str, StageAggregate]) -> str:
    pieces: List[str] = []
    for stage_name, aggregate in stages.items():
        stage_payload = {
            "stage": stage_name,
            "status": aggregate.status,
            "notes": aggregate.notes,
        }
        pieces.append(canonical_dumps(stage_payload) + "\n")
        for variant_name, variant in aggregate.variants.items():
            variant_payload = {
                "stage": stage_name,
                "variant": variant_name,
                "status": variant.status,
                "notes": variant.notes,
                "timestamp_utc": variant.timestamp,
            }
            pieces.append(canonical_dumps(variant_payload) + "\n")
    return hashlib.sha256("".join(pieces).encode("utf-8")).hexdigest()


def build_report(stages: Dict[str, StageAggregate]) -> Dict[str, object]:
    overall_status = (
        "PASS" if all(stage.status == "PASS" for stage in stages.values()) else "FAIL"
    )
    bundle_sha = compute_bundle_sha(stages)
    stages_block: Dict[str, Dict[str, object]] = {}
    for name, aggregate in stages.items():
        stages_block[name] = {
            "status": aggregate.status,
            "notes": aggregate.notes,
            "variants": {
                variant: {
                    "status": result.status,
                    "notes": result.notes,
                    "timestamp_utc": result.timestamp,
                }
                for variant, result in aggregate.variants.items()
            },
        }
    report = {
        "schema": "trendmarketv2.q1.boss.report",
        "schema_version": 2,
        "timestamp_utc": isoformat_utc(),
        "status": overall_status,
        "stages": stages_block,
        "bundle": {"sha256": bundle_sha},
    }
    schema = json.loads(SCHEMA_PATH.read_text(encoding="utf-8"))
    jsonschema.validate(instance=report, schema=schema)
    return report


def render_markdown(report: Dict[str, object]) -> str:
    lines = ["# Q1 Boss Final", ""]
    emoji = "✅" if report["status"] == "PASS" else "❌"
    lines.append(f"{emoji} Status geral: **{report['status']}**")
    lines.append("")
    lines.append("| Estágio | Primário | Clean | Notas |")
    lines.append("| --- | --- | --- | --- |")
    for stage in STAGES:
        entry = report["stages"][stage]
        primary = entry["variants"]["primary"]["status"]
        clean = entry["variants"]["clean"]["status"]
        status_icon = "✅" if entry["status"] == "PASS" else "❌"
        lines.append(
            "| {stage} | {primary} | {clean} | {icon} {notes} |".format(
                stage=stage.upper(),
                primary=primary,
                clean=clean,
                icon=status_icon,
                notes=entry["notes"],
            )
        )
    lines.append("")
    lines.append("## Próximos passos")
    failing = [s for s in STAGES if report["stages"][s]["status"] != "PASS"]
    if failing:
        for stage in failing:
            notes = report["stages"][stage]["notes"]
            lines.append(f"- {stage.upper()}: {notes}")
    else:
        lines.append("- Todos os estágios aprovados. Prosseguir com release interno.")
    lines.append("")
    lines.append(f"Bundle SHA256: `{report['bundle']['sha256']}`")
    return "\n".join(lines) + "\n"


def render_pr_comment(report: Dict[str, object]) -> str:
    emoji = "✅" if report["status"] == "PASS" else "❌"
    lines = [f"{emoji} [Q1 Boss Final report](./report.md)", ""]
    lines.append("![Status](./badge.svg)")
    lines.append("")
    lines.append("Resumo por estágio:")
    for stage in STAGES:
        entry = report["stages"][stage]
        icon = "✅" if entry["status"] == "PASS" else "❌"
        lines.append(f"- {icon} {stage.upper()}: {entry['notes']}")
    lines.append("")
    lines.append(f"Bundle SHA256: `{report['bundle']['sha256']}`")
    return "\n".join(lines) + "\n"


def render_badge(status: str) -> str:
    color = "2e8540" if status == "PASS" else "c92a2a"
    return (
        '<svg xmlns="http://www.w3.org/2000/svg" width="200" height="40">'
        f'<rect width="200" height="40" rx="6" fill="#{color}"/>'
        f'<text x="100" y="25" text-anchor="middle" fill="#ffffff" font-size="20"'
        ' font-family="Helvetica,Arial,sans-serif">Q1 Boss {status}</text>'.format(
            status=status
        )
        + "</svg>"
    )


def render_dag(report: Dict[str, object]) -> str:
    width = 140 * len(STAGES)
    height = 120
    svg: List[str] = [
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}">',
        "<style>text{font-family:Helvetica,Arial,sans-serif;font-size:14px;}"
        "line{stroke:#1f2933;stroke-width:2;}</style>",
    ]
    for index, stage in enumerate(STAGES):
        entry = report["stages"][stage]
        x = 70 + index * 140
        color = "#2e8540" if entry["status"] == "PASS" else "#c92a2a"
        svg.append(f'<circle cx="{x}" cy="45" r="30" fill="{color}" />')
        svg.append(
            f'<text x="{x}" y="50" text-anchor="middle" fill="#ffffff">{stage.upper()}</text>'
        )
        if index < len(STAGES) - 1:
            next_x = 70 + (index + 1) * 140
            svg.append(
                f'<line x1="{x + 30}" y1="45" x2="{next_x - 30}" y2="45" marker-end="url(#arrow)"/>'
            )
    svg.insert(
        1,
        '<defs><marker id="arrow" markerWidth="10" markerHeight="7" refX="10" refY="3.5" orient="auto"><polygon points="0 0, 10 3.5, 0 7" fill="#1f2933"/></marker></defs>',
    )
    svg.append("</svg>")
    return "".join(svg)


def write_outputs(report: Dict[str, object]) -> None:
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)
    (OUTPUT_DIR / "report.json").write_text(
        json.dumps(report, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )
    (OUTPUT_DIR / "report.md").write_text(render_markdown(report), encoding="utf-8")
    (OUTPUT_DIR / "pr_comment.md").write_text(
        render_pr_comment(report), encoding="utf-8"
    )
    (OUTPUT_DIR / "badge.svg").write_text(
        render_badge(str(report["status"])) + "\n", encoding="utf-8"
    )
    (OUTPUT_DIR / "dag.svg").write_text(render_dag(report) + "\n", encoding="utf-8")
    (OUTPUT_DIR / "guard_status.txt").write_text(
        f"{report['status']}\n", encoding="utf-8"
    )


def aggregate(_release_version: str | None = None) -> AggregateArtifacts:
    stages = collect_stages()
    report = build_report(stages)
    write_outputs(report)
    return AggregateArtifacts(report=report)


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Aggregate Q1 Boss Final stages")
    parser.add_argument(
        "--stages", type=Path, default=STAGES_DIR, help="Diretório contendo os estágios"
    )
    parser.add_argument(
        "--output", type=Path, default=OUTPUT_DIR, help="Diretório de saída"
    )
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    global STAGES_DIR
    global OUTPUT_DIR
    args = parse_args(argv or sys.argv[1:])
    if args.stages != STAGES_DIR:
        STAGES_DIR = args.stages
    if args.output != OUTPUT_DIR:
        OUTPUT_DIR = args.output
    report = aggregate()
    return 0 if report["status"] == "PASS" else 1


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main(sys.argv[1:]))
