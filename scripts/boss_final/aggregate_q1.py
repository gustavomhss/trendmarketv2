#!/usr/bin/env python3
from __future__ import annotations

import json
import hashlib
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Dict, Iterable, List, Mapping

BASE_DIR = Path(__file__).resolve().parents[2]
STAGES_DIR = BASE_DIR / "out" / "q1_boss_final" / "stages"
OUTPUT_DIR = BASE_DIR / "out" / "q1_boss_final"
ERROR_PREFIX = "BOSS-E"
SCHEMA_VERSION = 1
RESULT_FILENAME = "result.json"
GUARD_FILENAME = "guard_status.txt"
STAGES: tuple[str, ...] = ("s1", "s2", "s3", "s4", "s5", "s6")


@dataclass(frozen=True)
class StagePayload:
    stage: str
    status: str
    notes: str
    raw: Dict[str, object]


def fail(code: str, message: str) -> None:
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)
    (OUTPUT_DIR / GUARD_FILENAME).write_text("FAIL\n", encoding="utf-8")
    raise SystemExit(f"{ERROR_PREFIX}-{code}:{message}")


def load_stage_guard_status(stage: str) -> str:
    path = STAGES_DIR / stage / GUARD_FILENAME
    if not path.exists():
        fail("STAGE-GUARD-MISSING", f"Guard status ausente para {stage}: {path}")
    try:
        status = path.read_text(encoding="utf-8").strip().upper()
    except OSError as exc:
        fail("STAGE-GUARD-IO", f"Falha ao ler guard status de {stage}: {exc}")
    if status not in {"PASS", "FAIL"}:
        fail("STAGE-GUARD-INVALID", f"Valor inválido em guard status de {stage}: {status}")
    return status


def load_stage(stage: str) -> StagePayload:
    path = STAGES_DIR / stage / RESULT_FILENAME
    if not path.exists():
        fail("STAGE-RESULT-MISSING", f"Arquivo do estágio ausente: {path}")
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        fail("STAGE-RESULT-INVALID", f"JSON inválido em {path}: {exc}")

    schema_version = data.get("schema_version")
    if schema_version != SCHEMA_VERSION:
        fail("STAGE-SCHEMA", f"schema_version inesperado para {stage}: {schema_version}")

    declared_stage = str(data.get("stage", "")).lower()
    if declared_stage != stage:
        fail("STAGE-MISMATCH", f"ID do estágio divergente em {stage}: {declared_stage}")

    status = str(data.get("status", "")).upper()
    if status not in {"PASS", "FAIL"}:
        fail("STAGE-STATUS", f"Status inválido em {stage}: {status}")

    notes = data.get("notes")
    if not isinstance(notes, str):
        fail("STAGE-NOTES", f"Notas inválidas em {stage}: {notes!r}")
    notes = notes.strip()

    guard_status = load_stage_guard_status(stage)
    if guard_status != status:
        fail(
            "STAGE-GUARD-DIVERGENCE",
            f"Guard status {guard_status} difere do resultado {status} em {stage}",
        )

    return StagePayload(stage=stage, status=status, notes=notes, raw=data)


def load_all_stages() -> List[StagePayload]:
    return [load_stage(stage) for stage in STAGES]


def build_report(stages: Iterable[StagePayload]) -> Dict[str, object]:
    stage_map: Dict[str, StagePayload] = {payload.stage: payload for payload in stages}
    if set(stage_map) != set(STAGES):
        missing = sorted(set(STAGES) - set(stage_map))
        fail("STAGE-MISSING", f"Estágios ausentes: {missing}")

    timestamp = datetime.now(timezone.utc).replace(microsecond=0).isoformat()
    sprints: Dict[str, Dict[str, str]] = {}
    overall = "PASS"
    for stage in STAGES:
        payload = stage_map[stage]
        sprints[stage] = {
            "status": payload.status,
            "notes": payload.notes,
        }
        if payload.status != "PASS":
            overall = "FAIL"

    return {
        "schema_version": SCHEMA_VERSION,
        "timestamp_utc": timestamp,
        "sprints": sprints,
        "status": overall,
    }


def compute_bundle_hash(report: Mapping[str, object]) -> str:
    canonical = {
        "status": report["status"],
        "sprints": report["sprints"],
    }
    payload = json.dumps(
        canonical,
        ensure_ascii=False,
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def render_markdown(report: Mapping[str, object], stages: Iterable[StagePayload], bundle_hash: str) -> str:
    stage_map = {payload.stage: payload for payload in stages}
    lines: List[str] = ["# Q1 Boss Final", ""]
    emoji = "✅" if report["status"] == "PASS" else "❌"
    lines.append(f"{emoji} Status geral: **{report['status']}**")
    lines.append(f"- Timestamp (UTC): {report['timestamp_utc']}")
    lines.append(f"- Bundle SHA-256: `{bundle_hash}`")
    lines.append("")

    for stage in STAGES:
        entry = report["sprints"][stage]
        payload = stage_map[stage]
        stage_emoji = "✅" if entry["status"] == "PASS" else "❌"
        lines.append(f"## {stage.upper()}")
        lines.append(f"- Status: {stage_emoji} {entry['status']}")
        lines.append(f"- Notes: {entry['notes'] or 'n/a'}")
        checks = payload.raw.get("checks")
        if isinstance(checks, list) and checks:
            lines.append("- Checks:")
            for check in checks:
                check_name = str(check.get("name", "?"))
                check_status = str(check.get("status", "?")).upper()
                check_emoji = "✅" if check_status == "PASS" else "❌"
                detail = str(check.get("detail", "")).replace("\n", " ")
                lines.append(f"  - {check_emoji} {check_name}: {detail}")
        metadata = payload.raw.get("metadata")
        if isinstance(metadata, dict) and metadata:
            lines.append("- Metadata:")
            for key, value in sorted(metadata.items()):
                lines.append(f"  - {key}: {value}")
        lines.append("")

    return "\n".join(lines).rstrip() + "\n"


def render_badge(report: Mapping[str, object]) -> str:
    status = report["status"]
    color = "#2e8540" if status == "PASS" else "#c92a2a"
    return (
        "<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"180\" height=\"40\">"
        f"<rect width=\"180\" height=\"40\" fill=\"{color}\" rx=\"6\"/>"
        "<text x=\"90\" y=\"25\" text-anchor=\"middle\" fill=\"#ffffff\" font-size=\"20\""
        f" font-family=\"Helvetica,Arial,sans-serif\">Q1 {status}</text>"
        "</svg>"
    )


def render_dag(report: Mapping[str, object]) -> str:
    width = 120 * len(STAGES)
    height = 120
    svg = [
        f"<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"{width}\" height=\"{height}\">",
        "<defs><marker id=\"arrow\" markerWidth=\"10\" markerHeight=\"7\" refX=\"10\" refY=\"3.5\" orient=\"auto\"><polygon points=\"0 0, 10 3.5, 0 7\" fill=\"#1f2933\"/></marker></defs>",
        "<style>text{font-family:Helvetica,Arial,sans-serif;font-size:14px;}</style>",
    ]
    for index, stage in enumerate(STAGES):
        entry = report["sprints"][stage]
        x = 60 + index * 120
        status = entry["status"]
        color = "#2e8540" if status == "PASS" else "#c92a2a"
        svg.append(f"<circle cx=\"{x}\" cy=\"40\" r=\"30\" fill=\"{color}\" />")
        svg.append(
            f"<text x=\"{x}\" y=\"45\" text-anchor=\"middle\" fill=\"#ffffff\">{stage.upper()}</text>"
        )
        if index < len(STAGES) - 1:
            next_x = 60 + (index + 1) * 120
            svg.append(
                f"<line x1=\"{x + 30}\" y1=\"40\" x2=\"{next_x - 30}\" y2=\"40\" stroke=\"#1f2933\" stroke-width=\"2\" marker-end=\"url(#arrow)\" />"
            )
    svg.append("</svg>")
    return "".join(svg)


def build_pr_comment(report: Mapping[str, object]) -> str:
    emoji = "✅" if report["status"] == "PASS" else "❌"
    lines = [f"{emoji} **Q1 Boss Final** — {report['status']}"]
    lines.append(f"- Timestamp (UTC): {report['timestamp_utc']}")
    for stage in STAGES:
        entry = report["sprints"][stage]
        stage_emoji = "✅" if entry["status"] == "PASS" else "❌"
        notes = entry["notes"] or "n/a"
        lines.append(f"- {stage.upper()}: {stage_emoji} {notes}")
    return "\n".join(lines) + "\n"


def write_outputs(report: Dict[str, object], stages: Iterable[StagePayload]) -> str:
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)
    bundle_hash = compute_bundle_hash(report)
    (OUTPUT_DIR / "report.json").write_text(
        json.dumps(report, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    (OUTPUT_DIR / "report.md").write_text(
        render_markdown(report, stages, bundle_hash),
        encoding="utf-8",
    )
    (OUTPUT_DIR / "bundle.sha256").write_text(bundle_hash + "\n", encoding="utf-8")
    (OUTPUT_DIR / "badge.svg").write_text(render_badge(report) + "\n", encoding="utf-8")
    (OUTPUT_DIR / "dag.svg").write_text(render_dag(report) + "\n", encoding="utf-8")
    (OUTPUT_DIR / "pr_comment.md").write_text(build_pr_comment(report), encoding="utf-8")
    (OUTPUT_DIR / GUARD_FILENAME).write_text(report["status"] + "\n", encoding="utf-8")
    return bundle_hash


def main(argv: Iterable[str] | None = None) -> int:
    stages = load_all_stages()
    report = build_report(stages)
    write_outputs(report, stages)
    print(f"{report['status']} Q1 Boss Final")
    return 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
