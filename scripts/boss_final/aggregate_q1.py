#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, List

BASE_DIR = Path(__file__).resolve().parents[2]
STAGES_DIR = BASE_DIR / "out" / "q1_boss_final" / "stages"
OUTPUT_DIR = BASE_DIR / "out" / "q1_boss_final"
ERROR_PREFIX = "BOSS-E"
STAGES = ["s1", "s2", "s3", "s4", "s5", "s6"]


def ensure_output_dir() -> None:
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)


def fail(code: str, message: str) -> None:
    ensure_output_dir()
    (OUTPUT_DIR / "guard_status.txt").write_text("FAIL\n", encoding="utf-8")
    print(f"FAIL {ERROR_PREFIX}-{code}:{message}")
    raise SystemExit(1)


def load_stage(stage: str) -> Dict[str, Any]:
    path = STAGES_DIR / f"{stage}.json"
    if not path.exists():
        fail("STAGE-MISSING", f"Arquivo do estágio ausente: {path}")
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        fail("STAGE-INVALID", f"JSON inválido em {path}: {exc}")
    required = {"schema_version", "stage", "status", "notes", "generated_at"}
    if not required.issubset(data):
        missing = sorted(required - set(data))
        fail("STAGE-SCHEMA", f"Campos ausentes para {stage}: {missing}")
    if data["schema_version"] != 1:
        fail(
            "STAGE-VERSION",
            f"schema_version inesperado para {stage}: {data['schema_version']}",
        )
    if data["stage"].lower() != stage:
        fail("STAGE-MISMATCH", f"ID do estágio divergente em {stage}")
    status = str(data["status"]).upper()
    if status not in {"PASS", "FAIL"}:
        fail("STAGE-STATUS", f"Status inválido para {stage}: {data['status']}")
    notes = data.get("notes")
    if not isinstance(notes, str):
        fail("STAGE-NOTES", f"Notas inválidas para {stage}: {notes!r}")
    data["status"] = status
    data["notes"] = notes.strip()
    return data


def load_all_stages() -> Dict[str, Dict[str, Any]]:
    results: Dict[str, Dict[str, Any]] = {}
    for stage in STAGES:
        results[stage] = load_stage(stage)
    return results


def build_report(stage_payloads: Dict[str, Dict[str, Any]]) -> Dict[str, Any]:
    timestamp = datetime.now(timezone.utc).replace(microsecond=0).isoformat()
    sprints: Dict[str, Dict[str, str]] = {}
    statuses: List[str] = []
    for stage in STAGES:
        payload = stage_payloads[stage]
        status = payload["status"]
        notes = payload["notes"] or "Sem observações registradas."
        sprints[stage] = {"status": status, "notes": notes}
        statuses.append(status)
    overall = "PASS" if all(status == "PASS" for status in statuses) else "FAIL"
    return {
        "schema_version": 1,
        "timestamp_utc": timestamp,
        "sprints": sprints,
        "status": overall,
    }


def render_markdown(
    report: Dict[str, Any], stage_payloads: Dict[str, Dict[str, Any]]
) -> str:
    lines = ["# Q1 Boss Final", ""]
    lines.append(f"**Status geral:** {report['status']}")
    lines.append(f"**Gerado em:** {report['timestamp_utc']}")
    lines.append("")
    lines.append("| Estágio | Status | Observações |")
    lines.append("| --- | --- | --- |")
    for stage in STAGES:
        payload = stage_payloads[stage]
        status_icon = "✅" if payload["status"] == "PASS" else "❌"
        notes = payload["notes"].replace("|", "\\|").replace("\n", "<br />")
        lines.append(
            f"| {stage.upper()} | {status_icon} {payload['status']} | {notes} |"
        )
    lines.append("")
    lines.append("## Detalhes adicionais")
    any_details = False
    for stage in STAGES:
        details = stage_payloads[stage].get("details")
        if not details:
            continue
        any_details = True
        lines.append(f"### {stage.upper()}")
        lines.append("```json")
        lines.append(json.dumps(details, indent=2, ensure_ascii=False))
        lines.append("```")
        lines.append("")
    if not any_details:
        lines.append("Nenhum detalhe adicional disponível.")
    return "\n".join(lines).rstrip() + "\n"


def render_badge(report: Dict[str, Any]) -> str:
    color = "#2e8540" if report["status"] == "PASS" else "#c92a2a"
    return (
        '<svg xmlns="http://www.w3.org/2000/svg" width="220" height="40">'
        f'<rect width="220" height="40" fill="{color}" rx="6"/>'
        f'<text x="110" y="25" text-anchor="middle" fill="#ffffff" font-size="20"'
        f' font-family="Helvetica,Arial,sans-serif">Q1 BOSS {report["status"]}</text>'
        "</svg>"
    )


def render_dag(stage_payloads: Dict[str, Dict[str, Any]]) -> str:
    width = 140 * len(STAGES)
    height = 120
    nodes: List[str] = [
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}">',
        "<style>text{font-family:Helvetica,Arial,sans-serif;font-size:14px;}</style>",
        '<defs><marker id="arrow" markerWidth="10" markerHeight="7" refX="10" refY="3.5" orient="auto"><polygon points="0 0, 10 3.5, 0 7" fill="#1f2933"/></marker></defs>',
    ]
    for index, stage in enumerate(STAGES):
        payload = stage_payloads[stage]
        x = 70 + index * 140
        color = "#2e8540" if payload["status"] == "PASS" else "#c92a2a"
        nodes.append(f'<circle cx="{x}" cy="40" r="35" fill="{color}" />')
        nodes.append(
            f'<text x="{x}" y="45" text-anchor="middle" fill="#ffffff">{stage.upper()} {payload["status"]}</text>'
        )
        if index < len(STAGES) - 1:
            next_x = 70 + (index + 1) * 140
            nodes.append(
                f'<line x1="{x + 35}" y1="40" x2="{next_x - 35}" y2="40" stroke="#1f2933" stroke-width="2" marker-end="url(#arrow)" />'
            )
    nodes.append("</svg>")
    return "".join(nodes)


def build_pr_comment(
    report: Dict[str, Any], stage_payloads: Dict[str, Dict[str, Any]]
) -> str:
    lines = [
        f"{'✅' if report['status'] == 'PASS' else '❌'} [Q1 Boss Final report](./report.md)",
        "",
    ]
    lines.append("![Status](./badge.svg)")
    lines.append("")
    lines.append("## Observações por sprint")
    for stage in STAGES:
        payload = stage_payloads[stage]
        prefix = "✅" if payload["status"] == "PASS" else "❌"
        lines.append(f"- {prefix} {stage.upper()}: {payload['notes']}")
    lines.append("")
    lines.append(f"Status geral: **{report['status']}**")
    return "\n".join(lines).rstrip() + "\n"


def write_outputs(
    report: Dict[str, Any], stage_payloads: Dict[str, Dict[str, Any]]
) -> None:
    ensure_output_dir()
    (OUTPUT_DIR / "report.json").write_text(
        json.dumps(report, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )
    (OUTPUT_DIR / "report.md").write_text(
        render_markdown(report, stage_payloads), encoding="utf-8"
    )
    (OUTPUT_DIR / "badge.svg").write_text(render_badge(report) + "\n", encoding="utf-8")
    (OUTPUT_DIR / "dag.svg").write_text(
        render_dag(stage_payloads) + "\n", encoding="utf-8"
    )
    (OUTPUT_DIR / "pr_comment.md").write_text(
        build_pr_comment(report, stage_payloads), encoding="utf-8"
    )
    canonical = json.dumps(
        report, sort_keys=True, ensure_ascii=False, separators=(",", ":")
    ).encode("utf-8")
    digest = hashlib.sha256(canonical).hexdigest()
    (OUTPUT_DIR / "bundle.sha256").write_text(digest + "\n", encoding="utf-8")
    (OUTPUT_DIR / "guard_status.txt").write_text(
        report["status"] + "\n", encoding="utf-8"
    )


def main() -> int:
    stage_payloads = load_all_stages()
    report = build_report(stage_payloads)
    write_outputs(report, stage_payloads)
    if report["status"] == "PASS":
        print("PASS Q1 Boss Final")
    else:
        print("FAIL Q1 Boss Final")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
