#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Dict, Iterable, List

BASE_DIR = Path(__file__).resolve().parents[2]
OUTPUT_DIR = BASE_DIR / "out" / "q1_boss_final"
STAGES_DIR = OUTPUT_DIR / "stages"
STAGES: Iterable[str] = ("s1", "s2", "s3", "s4", "s5", "s6")
ERROR_PREFIX = "BOSS-E"


@dataclass(frozen=True)
class StageResult:
    stage: str
    status: str
    notes: str
    timestamp_utc: str
    details: Dict[str, object]


def fail(code: str, message: str) -> None:
    print(f"FAIL {ERROR_PREFIX}-{code}:{message}")
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)
    (OUTPUT_DIR / "guard_status.txt").write_text("FAIL\n", encoding="utf-8")
    raise SystemExit(1)


def read_guard_status(path: Path) -> str:
    if not path.exists():
        fail("STAGE-GUARD", f"Arquivo guard_status ausente: {path}")
    status = path.read_text(encoding="utf-8").strip().upper()
    if status not in {"PASS", "FAIL"}:
        fail("STAGE-GUARD", f"Status inválido em {path}: {status!r}")
    return status


def load_stage(stage: str) -> StageResult:
    stage_dir = STAGES_DIR / stage
    if not stage_dir.exists():
        fail("STAGE-DIR", f"Diretório do estágio ausente: {stage_dir}")
    guard_status = read_guard_status(stage_dir / "guard_status.txt")
    result_path = stage_dir / "result.json"
    try:
        result = json.loads(result_path.read_text(encoding="utf-8"))
    except FileNotFoundError:
        fail("STAGE-RESULT", f"result.json ausente para {stage}")
    except json.JSONDecodeError as exc:
        fail("STAGE-RESULT", f"JSON inválido em {result_path}: {exc}")

    required = {"schema_version", "stage", "status", "notes", "timestamp_utc"}
    missing = required - result.keys()
    if missing:
        fail("STAGE-SCHEMA", f"Campos ausentes em {stage}: {sorted(missing)}")
    if result["schema_version"] != 1:
        fail("STAGE-SCHEMA", f"schema_version inesperado em {stage}: {result['schema_version']}")
    if result["stage"] != stage:
        fail("STAGE-MISMATCH", f"Identificador divergente em {stage}")
    status = str(result["status"]).upper()
    if status not in {"PASS", "FAIL"}:
        fail("STAGE-STATUS", f"Status inválido em {stage}: {status!r}")
    if status != guard_status:
        fail("STAGE-STATUS", f"Divergência entre guard_status e result.json em {stage}")
    notes = str(result["notes"]).strip()
    if not notes:
        fail("STAGE-NOTES", f"Notas vazias para {stage}")
    timestamp = str(result["timestamp_utc"]).strip()
    if not timestamp:
        fail("STAGE-TIMESTAMP", f"timestamp_utc inválido para {stage}")
    details_raw = result.get("details", {})
    if details_raw is None:
        details_raw = {}
    if not isinstance(details_raw, dict):
        fail("STAGE-DETAILS", f"Campo details inválido em {stage}")
    return StageResult(stage=stage, status=status, notes=notes, timestamp_utc=timestamp, details=details_raw)


def load_all_stages() -> List[StageResult]:
    return [load_stage(stage) for stage in STAGES]


def build_report(stages: List[StageResult]) -> Dict[str, object]:
    timestamp = datetime.now(timezone.utc).replace(microsecond=0).isoformat()
    sprints = {
        result.stage: {
            "status": result.status,
            "notes": result.notes,
        }
        for result in stages
    }
    overall = "PASS" if all(result.status == "PASS" for result in stages) else "FAIL"
    return {
        "schema_version": 1,
        "timestamp_utc": timestamp,
        "sprints": sprints,
        "status": overall,
    }


def sanitize_notes(notes: str) -> str:
    return notes.replace("\r", "").replace("\n", "<br />")


def render_markdown(report: Dict[str, object], stages: List[StageResult]) -> str:
    lines: List[str] = ["# Q1 Boss Final", ""]
    status = report["status"]
    emoji = "✅" if status == "PASS" else "❌"
    lines.append(f"{emoji} **Status geral:** {status}")
    lines.append(f"- Gerado em: {report['timestamp_utc']}")
    lines.append("")
    lines.append("| Estágio | Status | Notas | Timestamp |")
    lines.append("| --- | --- | --- | --- |")
    for result in stages:
        lines.append(
            f"| {result.stage.upper()} | {result.status} | {sanitize_notes(result.notes)} | {result.timestamp_utc} |"
        )
    lines.append("")
    failing = [result for result in stages if result.status != "PASS"]
    lines.append("## Próximos passos")
    if failing:
        for item in failing:
            lines.append(f"- {item.stage.upper()}: {item.notes}")
    else:
        lines.append("- Todos os estágios passaram. Prosseguir com checklist de release.")
    return "\n".join(lines) + "\n"


def render_badge(report: Dict[str, object]) -> str:
    status = report["status"]
    color = "#2e8540" if status == "PASS" else "#c92a2a"
    return (
        "<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"200\" height=\"40\">"
        f"<rect width=\"200\" height=\"40\" fill=\"{color}\" rx=\"6\"/>"
        f"<text x=\"100\" y=\"25\" text-anchor=\"middle\" fill=\"#ffffff\" font-size=\"20\""
        " font-family=\"Helvetica,Arial,sans-serif\">Q1 {status}</text>"
        "</svg>"
    )


def render_dag(stages: List[StageResult]) -> str:
    width = 140 * len(stages)
    height = 120
    svg = [
        f"<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"{width}\" height=\"{height}\">",
        "<style>text{font-family:Helvetica,Arial,sans-serif;font-size:14px;}</style>",
        "<defs><marker id=\"arrow\" markerWidth=\"10\" markerHeight=\"7\" refX=\"10\" refY=\"3.5\" orient=\"auto\"><polygon points=\"0 0, 10 3.5, 0 7\" fill=\"#1f2933\"/></marker></defs>",
    ]
    for index, result in enumerate(stages):
        x = 70 + index * 140
        color = "#2e8540" if result.status == "PASS" else "#c92a2a"
        svg.append(f"<circle cx=\"{x}\" cy=\"40\" r=\"35\" fill=\"{color}\" />")
        svg.append(
            f"<text x=\"{x}\" y=\"45\" text-anchor=\"middle\" fill=\"#ffffff\">{result.stage.upper()}</text>"
        )
        if index < len(stages) - 1:
            next_x = 70 + (index + 1) * 140
            svg.append(
                f"<line x1=\"{x + 35}\" y1=\"40\" x2=\"{next_x - 35}\" y2=\"40\" stroke=\"#1f2933\" stroke-width=\"2\" marker-end=\"url(#arrow)\" />"
            )
    svg.append("</svg>")
    return "".join(svg)


def build_pr_comment(report: Dict[str, object], stages: List[StageResult]) -> str:
    emoji = "✅" if report["status"] == "PASS" else "❌"
    lines = [f"{emoji} Q1 Boss Final — {report['status']}", ""]
    lines.append("| Estágio | Status | Notas |")
    lines.append("| --- | --- | --- |")
    for result in stages:
        lines.append(
            f"| {result.stage.upper()} | {result.status} | {sanitize_notes(result.notes)} |"
        )
    lines.append("")
    failing = [item for item in stages if item.status != "PASS"]
    if failing:
        lines.append("### Ações prioritárias")
        for item in failing:
            lines.append(f"- {item.stage.upper()}: {item.notes}")
        lines.append("")
    lines.append("Detalhes completos em [report.md](./report.md).")
    return "\n".join(lines) + "\n"


def write_outputs(report: Dict[str, object], stages: List[StageResult]) -> None:
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)
    (OUTPUT_DIR / "report.json").write_text(
        json.dumps(report, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    (OUTPUT_DIR / "report.md").write_text(render_markdown(report, stages), encoding="utf-8")
    (OUTPUT_DIR / "badge.svg").write_text(render_badge(report) + "\n", encoding="utf-8")
    (OUTPUT_DIR / "dag.svg").write_text(render_dag(stages) + "\n", encoding="utf-8")
    (OUTPUT_DIR / "pr_comment.md").write_text(build_pr_comment(report, stages), encoding="utf-8")
    canonical = json.dumps(report, sort_keys=True, ensure_ascii=False, separators=(",", ":")).encode("utf-8")
    (OUTPUT_DIR / "bundle.sha256").write_text(hashlib.sha256(canonical).hexdigest() + "\n", encoding="utf-8")
    (OUTPUT_DIR / "guard_status.txt").write_text(report["status"] + "\n", encoding="utf-8")


def main() -> int:
    stages = load_all_stages()
    report = build_report(stages)
    write_outputs(report, stages)
    print(f"{report['status']} Q1 Boss Final")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
