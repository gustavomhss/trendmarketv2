#!/usr/bin/env python3
from __future__ import annotations

import json
from dataclasses import dataclass
from datetime import datetime, timezone
from hashlib import sha256
from pathlib import Path
from typing import Dict, List, Sequence

BASE_DIR = Path(__file__).resolve().parents[2]
STAGES_DIR = BASE_DIR / "out" / "q1_boss_final" / "stages"
OUTPUT_DIR = BASE_DIR / "out" / "q1_boss_final"
ERROR_PREFIX = "BOSS-E"
STAGES: Sequence[str] = ("s1", "s2", "s3", "s4", "s5", "s6")


class AggregationFailure(Exception):
    def __init__(self, code: str, message: str) -> None:
        super().__init__(message)
        self.code = code
        self.message = message


@dataclass(frozen=True)
class VariantResult:
    stage: str
    variant: str
    status: str
    notes: str
    failure_code: str | None
STAGES = ["s1", "s2", "s3", "s4", "s5", "s6"]
STAGE_GUARD_SUFFIX = "_guard_status.txt"

SCHEMA_VERSION = 1


def fail(code: str, message: str) -> None:
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)
    (OUTPUT_DIR / "guard_status.txt").write_text("FAIL\n", encoding="utf-8")
    print(f"FAIL {ERROR_PREFIX}-{code}:{message}")
    raise SystemExit(1)


def ensure_stage_dir(stage: str) -> Path:
    stage_dir = STAGES_DIR / stage
    if not stage_dir.exists():
        raise AggregationFailure("STAGE-MISSING", f"Diretório ausente para {stage}: {stage_dir}")
    return stage_dir


def load_variant(stage: str, variant_dir: Path) -> VariantResult:
    guard_path = variant_dir / "guard_status.txt"
    result_path = variant_dir / "result.json"
    if not guard_path.exists():
        raise AggregationFailure("VARIANT-GUARD", f"guard_status.txt ausente em {variant_dir}")
    if not result_path.exists():
        raise AggregationFailure("VARIANT-RESULT", f"result.json ausente em {variant_dir}")
    guard = guard_path.read_text(encoding="utf-8").strip().upper()
    if guard not in {"PASS", "FAIL"}:
        raise AggregationFailure("VARIANT-GUARD", f"valor inválido em {guard_path}: {guard}")
    try:
        result = json.loads(result_path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        raise AggregationFailure("VARIANT-JSON", f"JSON inválido em {result_path}: {exc}") from exc
    if result.get("stage") != stage:
        raise AggregationFailure("VARIANT-STAGE", f"Stage inconsistente em {result_path}")
    variant = result.get("variant", variant_dir.name)
    status = result.get("status", "").upper()
    if status != guard:
        raise AggregationFailure("VARIANT-MISMATCH", f"guard_status divergente em {variant_dir}")
    notes = (result.get("notes") or "").strip()
    failure_code = result.get("failure_code")
    if failure_code is not None:
        failure_code = str(failure_code)
    return VariantResult(stage=stage, variant=variant, status=status, notes=notes, failure_code=failure_code)


def load_stage(stage: str) -> Dict[str, object]:
    stage_dir = ensure_stage_dir(stage)
    variant_dirs = sorted([path for path in stage_dir.iterdir() if path.is_dir()])
    if not variant_dirs:
        raise AggregationFailure("STAGE-VARIANTS", f"Nenhuma variante encontrada para {stage}")
    variants = [load_variant(stage, variant_dir) for variant_dir in variant_dirs]
    stage_status = "PASS" if all(item.status == "PASS" for item in variants) else "FAIL"
    parts: List[str] = []
    for item in variants:
        prefix = item.variant.upper()
        if item.failure_code and item.status != "PASS":
            prefix = f"{prefix} [{item.failure_code}]"
        snippet = item.notes or ("OK" if item.status == "PASS" else "Sem notas")
        parts.append(f"{prefix}: {snippet}")
    notes = "; ".join(parts)
    return {
        "stage": stage,
        "status": stage_status,
        "notes": notes,
        "variants": [item.__dict__ for item in variants],
    }


def load_all_stages() -> List[Dict[str, object]]:
    stages: List[Dict[str, object]] = []
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
        try:
            stages.append(load_stage(stage))
        except AggregationFailure as exc:
            fail(exc.code, exc.message)
    return stages


def build_report(stages: List[Dict[str, object]]) -> Dict[str, object]:
    timestamp = datetime.now(timezone.utc).replace(microsecond=0).isoformat()
    sprints: Dict[str, Dict[str, str]] = {}
    global_status = "PASS"
    for stage in stages:
        sprints[stage["stage"]] = {
            "status": stage["status"],
            "notes": stage["notes"],
        }
        if stage["status"] != "PASS":
            global_status = "FAIL"
    return {
        "schema_version": 1,
        "timestamp_utc": timestamp,
        "sprints": sprints,
        "status": global_status,
    }


def write_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def render_markdown(report: Dict[str, object], stages: List[Dict[str, object]], bundle_hash: str) -> str:
    lines = ["# Q1 Boss Final", ""]
    lines.append(f"Status global: **{report['status']}**")
    lines.append("")
    lines.append("| Stage | Status | Notas |")
    lines.append("| --- | --- | --- |")
    for stage in stages:
        stage_name = stage["stage"].upper()
        status = stage["status"]
        notes = stage["notes"].replace("|", "\\|")
        lines.append(f"| {stage_name} | {status} | {notes} |")
    lines.append("")
    lines.append(f"- Timestamp (UTC): {report['timestamp_utc']}")
    lines.append(f"- Bundle SHA256: `{bundle_hash}`")
    return "\n".join(lines) + "\n"


def render_badge(status: str) -> str:
    color = "#2e8540" if status == "PASS" else "#c92a2a"
    return (
        "<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"200\" height=\"40\">"
        f"<rect width=\"200\" height=\"40\" fill=\"{color}\" rx=\"6\"/>"
        f"<text x=\"100\" y=\"25\" text-anchor=\"middle\" fill=\"#ffffff\" font-size=\"20\" font-family=\"Helvetica,Arial,sans-serif\">Q1 {status}</text>"
        "</svg>"
    )


def render_dag(stages: List[Dict[str, object]]) -> str:
    width = 120 * len(stages)
    height = 120
    svg = [
        f"<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"{width}\" height=\"{height}\">",
        "<style>text{font-family:Helvetica,Arial,sans-serif;font-size:14px;}</style>",
        "<defs><marker id=\"arrow\" markerWidth=\"10\" markerHeight=\"7\" refX=\"10\" refY=\"3.5\" orient=\"auto\"><polygon points=\"0 0, 10 3.5, 0 7\" fill=\"#1f2933\"/></marker></defs>",
    ]
    for index, stage in enumerate(stages):
        x = 60 + index * 120
        status_color = "#2e8540" if stage["status"] == "PASS" else "#c92a2a"
        svg.append(f"<circle cx=\"{x}\" cy=\"40\" r=\"30\" fill=\"{status_color}\" />")
        svg.append(f"<text x=\"{x}\" y=\"45\" text-anchor=\"middle\" fill=\"#ffffff\">{stage['stage'].upper()}</text>")
        if index < len(stages) - 1:
            next_x = 60 + (index + 1) * 120
            svg.append(
                f"<line x1=\"{x + 30}\" y1=\"40\" x2=\"{next_x - 30}\" y2=\"40\" stroke=\"#1f2933\" stroke-width=\"2\" marker-end=\"url(#arrow)\" />"
            )
    svg.append("</svg>")
    return "".join(svg)


def render_pr_comment(report: Dict[str, object], stages: List[Dict[str, object]], bundle_hash: str) -> str:
    emoji = "✅" if report["status"] == "PASS" else "❌"
    lines = [f"{emoji} Q1 Boss Final", "", "| Stage | Status | Notas |", "| --- | --- | --- |"]
    for stage in stages:
        notes = stage["notes"].replace("|", "\\|")
        lines.append(f"| {stage['stage'].upper()} | {stage['status']} | {notes} |")
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
        "schema_version": SCHEMA_VERSION,
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
    lines.append(f"Bundle SHA256: `{bundle_hash}`")
    lines.append("Detalhes completos em [report.md](./report.md).")
    return "\n".join(lines) + "\n"


def write_outputs(report: Dict[str, object], stages: List[Dict[str, object]]) -> None:
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)
    canonical = json.dumps(report, sort_keys=True, ensure_ascii=False, separators=(",", ":"))
    bundle_hash = sha256(canonical.encode("utf-8")).hexdigest()
    write_text(OUTPUT_DIR / "report.json", json.dumps(report, indent=2, ensure_ascii=False) + "\n")
    write_text(OUTPUT_DIR / "report.md", render_markdown(report, stages, bundle_hash))
    write_text(OUTPUT_DIR / "badge.svg", render_badge(report["status"]) + "\n")
    write_text(OUTPUT_DIR / "dag.svg", render_dag(stages) + "\n")
    write_text(OUTPUT_DIR / "pr_comment.md", render_pr_comment(report, stages, bundle_hash))
    write_text(OUTPUT_DIR / "bundle.sha256", bundle_hash + "\n")
    write_text(OUTPUT_DIR / "guard_status.txt", f"{report['status']}\n")


def main() -> int:
    try:
        stages = load_all_stages()
    except AggregationFailure as exc:
        fail(exc.code, exc.message)
    report = build_report(stages)
    write_outputs(report, stages)
    print(f"PASS Q1 Boss Final ({report['status']})")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
