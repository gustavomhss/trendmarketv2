#!/usr/bin/env python3
from __future__ import annotations

import json
import sys
from datetime import datetime, timezone
from decimal import Decimal, getcontext, ROUND_HALF_EVEN
from pathlib import Path
from typing import Dict, List

getcontext().prec = 28
getcontext().rounding = ROUND_HALF_EVEN

BASE_DIR = Path(__file__).resolve().parents[2]
STAGES_DIR = BASE_DIR / "out" / "q1_boss_final" / "stages"
OUTPUT_DIR = BASE_DIR / "out" / "q1_boss_final"
ERROR_PREFIX = "BOSS-E"

STAGES = ["s1", "s2", "s3", "s4", "s5", "s6"]
STAGE_GUARD_SUFFIX = "_guard_status.txt"


def fail(code: str, message: str) -> None:
    print(f"FAIL {ERROR_PREFIX}-{code}:{message}")
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)
    (OUTPUT_DIR / "guard_status.txt").write_text("FAIL\n", encoding="utf-8")
    raise SystemExit(1)


def load_stage(stage: str) -> Dict[str, str]:
    path = STAGES_DIR / f"{stage}.json"
    if not path.exists():
        fail("STAGE-MISSING", f"Arquivo do estágio ausente: {path}")
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        fail("STAGE-INVALID", f"JSON inválido em {path}: {exc}")
    required = {"schema_version", "stage", "status", "score", "formatted_score", "generated_at"}
    if not required.issubset(data):
        fail("STAGE-SCHEMA", f"Campos ausentes para {stage}: {sorted(required - set(data))}")
    if data["stage"].lower() != stage:
        fail("STAGE-MISMATCH", f"ID do estágio divergente em {stage}")
    guard_status = load_stage_guard_status(stage)
    if guard_status == "FAIL" and data["status"] != "fail":
        data["status"] = "fail"
    if guard_status == "PASS" and data["status"] == "fail":
        fail("STAGE-GUARD-DIVERGENCE", f"Guard status PASS mas estágio falhou: {stage}")
    return data


def load_stage_guard_status(stage: str) -> str:
    path = STAGES_DIR / f"{stage}{STAGE_GUARD_SUFFIX}"
    if not path.exists():
        fail("STAGE-GUARD-MISSING", f"Guard status ausente para {stage}: {path}")
    try:
        status = path.read_text(encoding="utf-8").strip().upper()
    except OSError as exc:
        fail("STAGE-GUARD-IO", f"Falha ao ler guard status de {stage}: {exc}")
    if status not in {"PASS", "FAIL"}:
        fail("STAGE-GUARD-INVALID", f"Valor inválido em guard status de {stage}: {status}")
    return status


def load_all_stages() -> List[Dict[str, str]]:
    results: List[Dict[str, str]] = []
    for stage in STAGES:
        results.append(load_stage(stage))
    return results


def decimal_from(value: str) -> Decimal:
    try:
        return Decimal(value)
    except Exception as exc:  # pragma: no cover
        fail("DECIMAL", f"Valor inválido {value}: {exc}")
        raise


def compute_summary(stages: List[Dict[str, str]]) -> Dict[str, object]:
    total = len(stages)
    passing = sum(1 for stage in stages if stage["status"] == "pass")
    failing = total - passing
    aggregate_ratio = Decimal("0")
    for stage in stages:
        aggregate_ratio += decimal_from(stage["score"])
    aggregate_ratio /= Decimal(total)
    aggregate_ratio = aggregate_ratio.quantize(Decimal("0.0001"))
    status = "pass" if failing == 0 else "fail"
    return {
        "status": status,
        "passing_stages": passing,
        "failing_stages": failing,
        "aggregate_ratio": str(aggregate_ratio),
        "formatted_ratio": f"{aggregate_ratio}",
        "total_stages": total,
    }


def render_markdown(report: Dict[str, object]) -> str:
    lines = ["# Q1 Boss Final", ""]
    summary = report["summary"]
    emoji = "✅" if summary["status"] == "pass" else "❌"
    lines.append(f"{emoji} Status geral: **{summary['status'].upper()}**")
    lines.append(f"- Razão agregada: {summary['formatted_ratio']}")
    lines.append("")
    lines.append("| Estágio | Status | Score | Gerado em | Próximo passo |")
    lines.append("| --- | --- | --- | --- | --- |")
    for stage in report["stages"]:
        status = "✅" if stage["status"] == "pass" else "❌"
        on_fail = stage.get("on_fail", "Monitorar continuamente.")
        lines.append(
            f"| {stage['stage'].upper()} | {status} | {stage['formatted_score']} | {stage['generated_at']} | {on_fail} |"
        )
    lines.append("")
    lines.append("## O que fazer agora")
    failing = [stage for stage in report["stages"] if stage["status"] != "pass"]
    if failing:
        for stage in failing:
            lines.append(f"- {stage['stage'].upper()}: {stage.get('on_fail', 'Ação corretiva pendente.')}")
    else:
        lines.append("- Todos os estágios passaram. Validar releases e seguir com o runbook de publicação.")
    lines.append("")
    lines.append("## Metadados")
    lines.append(f"- Gerado em: {report['generated_at']}")
    lines.append(f"- SHA do bundle: `{report['bundle_sha256']}`")
    return "\n".join(lines) + "\n"


def render_badge(report: Dict[str, object]) -> str:
    status = report["summary"]["status"]
    color = "#2e8540" if status == "pass" else "#c92a2a"
    text = "PASS" if status == "pass" else "FAIL"
    return (
        "<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"180\" height=\"40\">"
        f"<rect width=\"180\" height=\"40\" fill=\"{color}\" rx=\"6\"/>"
        "<text x=\"90\" y=\"25\" text-anchor=\"middle\" fill=\"#ffffff\" font-size=\"20\""
        f" font-family=\"Helvetica,Arial,sans-serif\">Q1 {text}</text>"
        "</svg>"
    )


def render_dag(stages: List[Dict[str, str]]) -> str:
    width = 120 * len(stages)
    height = 120
    svg = [
        f"<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"{width}\" height=\"{height}\">",
        "<style>text{font-family:Helvetica,Arial,sans-serif;font-size:14px;}</style>",
    ]
    for index, stage in enumerate(stages):
        x = 60 + index * 120
        status_color = "#2e8540" if stage["status"] == "pass" else "#c92a2a"
        svg.append(
            f"<circle cx=\"{x}\" cy=\"40\" r=\"30\" fill=\"{status_color}\" />"
            f"<text x=\"{x}\" y=\"45\" text-anchor=\"middle\" fill=\"#ffffff\">{stage['stage'].upper()}</text>"
        )
        if index < len(stages) - 1:
            next_x = 60 + (index + 1) * 120
            svg.append(
                f"<line x1=\"{x + 30}\" y1=\"40\" x2=\"{next_x - 30}\" y2=\"40\" stroke=\"#1f2933\" stroke-width=\"2\" marker-end=\"url(#arrow)\" />"
            )
    svg.insert(1, "<defs><marker id=\"arrow\" markerWidth=\"10\" markerHeight=\"7\" refX=\"10\" refY=\"3.5\" orient=\"auto\"><polygon points=\"0 0, 10 3.5, 0 7\" fill=\"#1f2933\"/></marker></defs>")
    svg.append("</svg>")
    return "".join(svg)


def build_report(stages: List[Dict[str, str]]) -> Dict[str, object]:
    generated_at = datetime.now(timezone.utc).replace(microsecond=0).isoformat()
    summary = compute_summary(stages)
    items = []
    for stage in stages:
        entry = {
            "stage": stage["stage"],
            "status": stage["status"],
            "score": stage["score"],
            "formatted_score": stage["formatted_score"],
            "generated_at": stage["generated_at"],
        }
        if "on_fail" in stage:
            entry["on_fail"] = stage["on_fail"]
        if "report_path" in stage:
            entry["report_path"] = stage["report_path"]
        if "bundle_sha256" in stage:
            entry["bundle_sha256"] = stage["bundle_sha256"]
        items.append(entry)
    bundle_content = json.dumps(items, sort_keys=True, ensure_ascii=False, separators=(",", ":")).encode("utf-8")
    bundle_hash = __import__("hashlib").sha256(bundle_content).hexdigest()
    return {
        "schema_version": 1,
        "generated_at": generated_at,
        "summary": summary,
        "stages": items,
        "bundle_sha256": bundle_hash,
    }


def build_pr_comment(report: Dict[str, object]) -> str:
    summary = report["summary"]
    emoji = "✅" if summary["status"] == "pass" else "❌"
    lines = [f"{emoji} [Q1 Boss Final report](./report.md)"]
    lines.append("")
    lines.append("![Status](./badge.svg)")
    lines.append("")
    lines.append("## O que fazer agora")
    failing = [stage for stage in report["stages"] if stage["status"] != "pass"]
    if failing:
        for stage in failing:
            lines.append(f"- {stage['stage'].upper()}: {stage.get('on_fail', 'Ação corretiva pendente.')}")
    else:
        lines.append("- Nenhuma ação pendente. Avançar com checklist de release.")
    lines.append("")
    lines.append("Detalhes completos em [report.md](./report.md).")
    return "\n".join(lines) + "\n"


def write_outputs(report: Dict[str, object]) -> None:
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)
    (OUTPUT_DIR / "report.json").write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    (OUTPUT_DIR / "report.md").write_text(render_markdown(report), encoding="utf-8")
    (OUTPUT_DIR / "badge.svg").write_text(render_badge(report) + "\n", encoding="utf-8")
    (OUTPUT_DIR / "dag.svg").write_text(render_dag(report["stages"]) + "\n", encoding="utf-8")
    (OUTPUT_DIR / "pr_comment.md").write_text(build_pr_comment(report), encoding="utf-8")
    (OUTPUT_DIR / "bundle.sha256").write_text(report["bundle_sha256"] + "\n", encoding="utf-8")
    status = "PASS" if report["summary"]["status"] == "pass" else "FAIL"
    (OUTPUT_DIR / "guard_status.txt").write_text(status + "\n", encoding="utf-8")


def main() -> int:
    stages = load_all_stages()
    report = build_report(stages)
    write_outputs(report)
    print("PASS Q1 Boss Final")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
