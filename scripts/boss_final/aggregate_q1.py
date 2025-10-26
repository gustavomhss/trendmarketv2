#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import json
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Dict

BASE_DIR = Path(__file__).resolve().parents[2]
if str(BASE_DIR) not in sys.path:
    sys.path.append(str(BASE_DIR))

import jsonschema
STAGES_DIR = BASE_DIR / "out" / "q1_boss_final" / "stages"
OUTPUT_DIR = BASE_DIR / "out" / "q1_boss_final"
SCHEMA_PATH = BASE_DIR / "schemas" / "q1_boss_report.schema.json"
STAGES = ("s1", "s2", "s3", "s4", "s5", "s6")


class BossError(RuntimeError):
    pass


def fail(code: str, message: str) -> None:
    print(f"FAIL BOSS-E-{code}:{message}")
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)
    (OUTPUT_DIR / "guard_status.txt").write_text("FAIL\n", encoding="utf-8")
    raise SystemExit(1)


def load_stage(stage: str) -> Dict[str, str]:
    stage_dir = STAGES_DIR / stage
    stage_file = stage_dir / "stage.json"
    guard_file = stage_dir / "guard_status.txt"
    if not stage_file.exists():
        fail("STAGE-MISSING", f"Arquivo stage.json ausente para {stage}")
    if not guard_file.exists():
        fail("GUARD-MISSING", f"guard_status.txt ausente para {stage}")
    try:
        data = json.loads(stage_file.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        fail("STAGE-INVALID", f"JSON inválido em {stage_file}: {exc}")
    required = {"stage", "status", "timestamp_utc", "notes"}
    if not required.issubset(data):
        missing = required - set(data)
        fail("STAGE-SCHEMA", f"Campos ausentes em {stage}: {sorted(missing)}")
    guard_status = guard_file.read_text(encoding="utf-8").strip()
    if guard_status not in {"PASS", "FAIL"}:
        fail("GUARD-VALUE", f"Valor inválido em guard_status de {stage}: {guard_status}")
    if data["stage"] != stage:
        fail("STAGE-MISMATCH", f"ID divergente em {stage}")
    if data["status"] != guard_status:
        fail("STATUS-MISMATCH", f"Status divergente em {stage}: stage.json={data['status']} guard={guard_status}")
    return {"status": data["status"], "notes": data["notes"]}


def load_stages() -> Dict[str, Dict[str, str]]:
    stages: Dict[str, Dict[str, str]] = {}
    for stage in STAGES:
        stages[stage] = load_stage(stage)
    return stages


def compute_bundle_sha(stages: Dict[str, Dict[str, str]]) -> str:
    payload = json.dumps(stages, sort_keys=True, ensure_ascii=False, separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def build_report(stages: Dict[str, Dict[str, str]]) -> Dict[str, object]:
    failing = any(entry["status"] != "PASS" for entry in stages.values())
    status = "FAIL" if failing else "PASS"
    report = {
        "schema_version": 1,
        "timestamp_utc": datetime.now(timezone.utc).replace(microsecond=0).isoformat(),
        "status": status,
        "sprints": stages,
        "bundle_sha256": compute_bundle_sha(stages),
    }
    schema = json.loads(SCHEMA_PATH.read_text(encoding="utf-8"))
    jsonschema.validate(instance=report, schema=schema)
    return report


def render_markdown(report: Dict[str, object]) -> str:
    lines = ["# Q1 Boss Final", ""]
    emoji = "✅" if report["status"] == "PASS" else "❌"
    lines.append(f"{emoji} Status geral: **{report['status']}**")
    lines.append("")
    lines.append("| Estágio | Status | Notas |")
    lines.append("| --- | --- | --- |")
    for stage in STAGES:
        entry = report["sprints"][stage]
        status_icon = "✅" if entry["status"] == "PASS" else "❌"
        lines.append(f"| {stage.upper()} | {status_icon} {entry['status']} | {entry['notes']} |")
    lines.append("")
    lines.append("## O que fazer agora")
    failing = [stage for stage in STAGES if report["sprints"][stage]["status"] != "PASS"]
    if failing:
        for stage in failing:
            notes = report["sprints"][stage]["notes"]
            lines.append(f"- {stage.upper()}: {notes}")
    else:
        lines.append("- Todos os estágios aprovados. Prosseguir com checklist de release.")
    lines.append("")
    lines.append("## Metadados")
    lines.append(f"- Gerado em: {report['timestamp_utc']}")
    lines.append(f"- SHA do bundle: `{report['bundle_sha256']}`")
    return "\n".join(lines) + "\n"


def render_badge(report: Dict[str, object]) -> str:
    color = "#2e8540" if report["status"] == "PASS" else "#c92a2a"
    return (
        "<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"180\" height=\"40\">"
        f"<rect width=\"180\" height=\"40\" fill=\"{color}\" rx=\"6\"/>"
        f"<text x=\"90\" y=\"25\" text-anchor=\"middle\" fill=\"#ffffff\" font-size=\"20\""
        " font-family=\"Helvetica,Arial,sans-serif\">Q1 {status}</text>".format(status=report["status"]) + "</svg>"
    )


def render_dag(report: Dict[str, object]) -> str:
    width = 120 * len(STAGES)
    height = 120
    svg = [
        f"<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"{width}\" height=\"{height}\">",
        "<style>text{font-family:Helvetica,Arial,sans-serif;font-size:14px;}</style>",
        "<defs><marker id=\"arrow\" markerWidth=\"10\" markerHeight=\"7\" refX=\"10\" refY=\"3.5\" orient=\"auto\"><polygon points=\"0 0, 10 3.5, 0 7\" fill=\"#1f2933\"/></marker></defs>",
    ]
    for index, stage in enumerate(STAGES):
        entry = report["sprints"][stage]
        x = 60 + index * 120
        color = "#2e8540" if entry["status"] == "PASS" else "#c92a2a"
        svg.append(f"<circle cx=\"{x}\" cy=\"40\" r=\"30\" fill=\"{color}\" />")
        svg.append(f"<text x=\"{x}\" y=\"45\" text-anchor=\"middle\" fill=\"#ffffff\">{stage.upper()}</text>")
        if index < len(STAGES) - 1:
            next_x = 60 + (index + 1) * 120
            svg.append(
                f"<line x1=\"{x + 30}\" y1=\"40\" x2=\"{next_x - 30}\" y2=\"40\" stroke=\"#1f2933\" stroke-width=\"2\" marker-end=\"url(#arrow)\" />"
            )
    svg.append("</svg>")
    return "".join(svg)


def build_pr_comment(report: Dict[str, object]) -> str:
    emoji = "✅" if report["status"] == "PASS" else "❌"
    lines = [f"{emoji} [Q1 Boss Final report](./report.md)"]
    lines.append("")
    lines.append("![Status](./badge.svg)")
    lines.append("")
    lines.append("## O que fazer agora")
    failing = [stage for stage in STAGES if report["sprints"][stage]["status"] != "PASS"]
    if failing:
        for stage in failing:
            notes = report["sprints"][stage]["notes"]
            lines.append(f"- {stage.upper()}: {notes}")
    else:
        lines.append("- Nenhuma ação pendente.")
    lines.append("")
    lines.append("Detalhes completos em [report.md](./report.md).")
    return "\n".join(lines) + "\n"


def write_outputs(report: Dict[str, object]) -> None:
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)
    (OUTPUT_DIR / "report.json").write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    (OUTPUT_DIR / "report.md").write_text(render_markdown(report), encoding="utf-8")
    (OUTPUT_DIR / "badge.svg").write_text(render_badge(report) + "\n", encoding="utf-8")
    (OUTPUT_DIR / "dag.svg").write_text(render_dag(report) + "\n", encoding="utf-8")
    (OUTPUT_DIR / "pr_comment.md").write_text(build_pr_comment(report), encoding="utf-8")
    (OUTPUT_DIR / "guard_status.txt").write_text(report["status"] + "\n", encoding="utf-8")


def main() -> int:
    stages = load_stages()
    report = build_report(stages)
    write_outputs(report)
    print(f"PASS Q1 Boss Final {report['status']}")
    return 0 if report["status"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
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
SCHEMA_VERSION = 2
ERROR_PREFIX = "BOSS-E"
REPORT_SCHEMA = "trendmarketv2.q1.boss.report"


@dataclass(frozen=True)
class StageSummary:
    stage: str
    status: str
    notes: str
    summary: Dict[str, object]
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
    if not guard_path.exists():
        raise RuntimeError(f"{ERROR_PREFIX}-E-GUARD: guard_status.txt ausente para {stage}/{variant}")
    guard = guard_path.read_text(encoding="utf-8").strip().upper()
    status = str(result.get("status", "FAIL")).upper()
    if guard not in {"PASS", "FAIL"}:
        raise RuntimeError(f"{ERROR_PREFIX}-E-GUARD: guard_status inválido para {stage}/{variant}")
    if status not in {"PASS", "FAIL"}:
        raise RuntimeError(f"{ERROR_PREFIX}-E-STATUS: status inválido em {stage}/{variant}")
    if status != guard:
        raise RuntimeError(f"{ERROR_PREFIX}-E-GUARD-MISMATCH: {stage}/{variant} guard {guard} != status {status}")
    result["status"] = status
    result["notes"] = str(result.get("notes", "")).strip()
    result.setdefault("guard_status", guard)
    return result


def load_stage_summary(stage: str) -> Dict[str, object]:
    directory = STAGES_DIR / stage
    summary_path = directory / "summary.json"
    guard_path = directory / "guard_status.txt"
    if not summary_path.exists():
        raise RuntimeError(f"{ERROR_PREFIX}-E-SUMMARY: summary.json ausente para {stage}")
    summary = load_json(summary_path)
    if not guard_path.exists():
        raise RuntimeError(f"{ERROR_PREFIX}-E-SUMMARY-GUARD: guard_status.txt ausente para {stage}")
    guard = guard_path.read_text(encoding="utf-8").strip().upper()
    status = str(summary.get("status", "FAIL")).upper()
    if status not in {"PASS", "FAIL"}:
        raise RuntimeError(f"{ERROR_PREFIX}-E-SUMMARY-STATUS: status inválido em {stage}")
    if guard not in {"PASS", "FAIL"}:
        raise RuntimeError(f"{ERROR_PREFIX}-E-SUMMARY-GUARD: guard inválido em {stage}")
    if status != guard:
        raise RuntimeError(f"{ERROR_PREFIX}-E-SUMMARY-MISMATCH: {stage} guard {guard} != summary {status}")
    summary["status"] = status
    summary["notes"] = str(summary.get("notes", "")).strip()
    return summary


def summarise_stage(stage: str) -> StageSummary:
    summary_payload = load_stage_summary(stage)
    variants: Dict[str, Dict[str, object]] = {}
    notes_parts: List[str] = []
    for variant in ("primary", "clean"):
        variant_result = load_stage_variant(stage, variant)
        variants[variant] = variant_result
        variant_note = variant_result.get("notes", "")
        notes_parts.append(
            f"{variant}:{variant_result['status']}{(' ' + variant_note) if variant_note else ''}"
        )
    stage_status = summary_payload.get("status", "FAIL").upper()
    if stage_status == "PASS":
        if any(variant_result["status"] != "PASS" for variant_result in variants.values()):
            raise RuntimeError(f"{ERROR_PREFIX}-E-SUMMARY-DRIFT: {stage} summary PASS mas variante falhou")
    notes = summary_payload.get("notes", "") or " | ".join(notes_parts)
    return StageSummary(
        stage=stage,
        status=stage_status,
        notes=str(notes).strip(),
        summary=summary_payload,
        variants=variants,
    )


def compute_bundle_sha(stage_summaries: Dict[str, StageSummary]) -> str:
    pieces: List[str] = []
    for stage in STAGES:
        summary = stage_summaries[stage]
        pieces.append(canonical_dumps(summary.summary))
        for variant in ("primary", "clean"):
            variant_payload = summary.variants[variant]
            pieces.append(
                canonical_dumps(
                    {
                        "stage": stage,
                        "variant": variant,
                        "status": variant_payload.get("status"),
                        "notes": variant_payload.get("notes"),
                        "timestamp_utc": variant_payload.get("timestamp_utc"),
                    }
                )
            )
    concatenated = "".join(pieces)
    return hashlib.sha256(concatenated.encode("utf-8")).hexdigest()


def build_report(stage_summaries: Dict[str, StageSummary], bundle_sha: str, release_tag: str | None) -> Dict[str, object]:
    report = {
        "schema": REPORT_SCHEMA,
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
