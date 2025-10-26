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
