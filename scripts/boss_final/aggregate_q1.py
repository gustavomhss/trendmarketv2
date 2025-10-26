#!/usr/bin/env python3
from __future__ import annotations

import json
from dataclasses import dataclass
from datetime import datetime, timezone
from decimal import Decimal, ROUND_HALF_EVEN, getcontext
from hashlib import sha256
from pathlib import Path
from typing import Dict, List, Sequence

BASE_DIR = Path(__file__).resolve().parents[2]
STAGES_DIR = BASE_DIR / "out" / "q1_boss_final" / "stages"
OUTPUT_DIR = BASE_DIR / "out" / "q1_boss_final"
ERROR_PREFIX = "BOSS-E"
SCHEMA_VERSION = 1
STAGES: Sequence[str] = ("s1", "s2", "s3", "s4", "s5", "s6")
STAGE_GUARD_SUFFIX = "_guard_status.txt"

getcontext().prec = 28
getcontext().rounding = ROUND_HALF_EVEN


class AggregationFailure(Exception):
    def __init__(self, code: str, message: str) -> None:
        super().__init__(message)
        self.code = code
        self.message = message


@dataclass(frozen=True)
class BossArtifacts:
    report: Dict[str, object]
    stages: List[Dict[str, object]]
    summary: Dict[str, object]
    bundle_sha256: str


def isoformat_utc() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def load_stage_guard_status(stage: str) -> str:
    path = STAGES_DIR / f"{stage}{STAGE_GUARD_SUFFIX}"
    if not path.exists():
        raise AggregationFailure("STAGE-GUARD-MISSING", f"Guard status ausente para {stage}: {path}")
    try:
        status = path.read_text(encoding="utf-8").strip().upper()
    except OSError as exc:
        raise AggregationFailure("STAGE-GUARD-IO", f"Falha ao ler guard status de {stage}: {exc}") from exc
    if status not in {"PASS", "FAIL"}:
        raise AggregationFailure("STAGE-GUARD-INVALID", f"Valor inválido em guard status de {stage}: {status}")
    return status


def load_stage(stage: str) -> Dict[str, object]:
    path = STAGES_DIR / f"{stage}.json"
    if not path.exists():
        raise AggregationFailure("STAGE-MISSING", f"Arquivo do estágio ausente: {path}")
    try:
        raw = path.read_text(encoding="utf-8")
    except OSError as exc:
        raise AggregationFailure("STAGE-IO", f"Falha ao ler {path}: {exc}") from exc
    try:
        data = json.loads(raw)
    except json.JSONDecodeError as exc:
        raise AggregationFailure("STAGE-INVALID", f"JSON inválido em {path}: {exc}") from exc
    required = {"schema_version", "stage", "status", "score", "formatted_score", "generated_at"}
    missing = sorted(required - data.keys())
    if missing:
        raise AggregationFailure("STAGE-SCHEMA", f"Campos ausentes para {stage}: {missing}")
    if int(data["schema_version"]) != 1:
        raise AggregationFailure("STAGE-SCHEMA", f"schema_version inválido em {path}")
    if str(data["stage"]).lower() != stage:
        raise AggregationFailure("STAGE-MISMATCH", f"ID do estágio divergente em {path}")
    guard_status = load_stage_guard_status(stage)
    status = str(data["status"]).upper()
    if guard_status == "FAIL":
        status = "FAIL"
    elif status == "FAIL":
        raise AggregationFailure("STAGE-GUARD-DIVERGENCE", f"Guard status PASS mas estágio falhou: {stage}")
    try:
        score = Decimal(str(data["score"]))
    except Exception as exc:  # pragma: no cover - defensive
        raise AggregationFailure("STAGE-SCORE", f"Score inválido em {path}: {exc}") from exc
    entry: Dict[str, object] = {
        "stage": stage,
        "status": status,
        "score": score,
        "formatted_score": str(data["formatted_score"]),
        "generated_at": str(data["generated_at"]),
        "guard_status": guard_status,
    }
    for key in ("notes", "on_fail", "report_path", "bundle_sha256"):
        if key in data:
            entry[key] = data[key]
    return entry


def load_all_stages() -> List[Dict[str, object]]:
    stages: List[Dict[str, object]] = []
    for stage in STAGES:
        stages.append(load_stage(stage))
    return stages


def compute_summary(stages: List[Dict[str, object]]) -> Dict[str, object]:
    if not stages:
        return {"status": "PASS", "aggregate_ratio": "0", "failing_stages": 0}
    scores = [entry["score"] for entry in stages]
    failing = sum(1 for entry in stages if entry["status"] != "PASS")
    aggregate = (sum(scores) / Decimal(len(scores))).quantize(Decimal("0.0001"))
    status = "PASS" if failing == 0 else "FAIL"
    return {
        "status": status,
        "aggregate_ratio": f"{aggregate}",
        "failing_stages": failing,
    }


def build_report(stages: List[Dict[str, object]], summary: Dict[str, object]) -> Dict[str, object]:
    sprints: Dict[str, Dict[str, str]] = {}
    for entry in stages:
        notes = str(entry.get("notes", "")).strip()
        sprints[entry["stage"]] = {
            "status": entry["status"],
            "notes": notes,
        }
    return {
        "schema_version": SCHEMA_VERSION,
        "timestamp_utc": isoformat_utc(),
        "status": summary["status"],
        "sprints": sprints,
    }


def render_markdown(
    report: Dict[str, object],
    stages: List[Dict[str, object]],
    summary: Dict[str, object],
    bundle_sha256: str,
) -> str:
    lines = ["# Q1 Boss Final", ""]
    lines.append(f"Status global: **{report['status']}**")
    lines.append(f"- Failing stages: {summary['failing_stages']}")
    lines.append(f"- Aggregate ratio: {summary['aggregate_ratio']}")
    lines.append(f"- Timestamp UTC: {report['timestamp_utc']}")
    lines.append(f"- Bundle SHA256: `{bundle_sha256}`")
    lines.append("")
    lines.append("| Stage | Status | Score | Notes |")
    lines.append("| --- | --- | --- | --- |")
    for entry in stages:
        notes = str(entry.get("notes", "")).replace("|", "\|")
        lines.append(
            f"| {entry['stage'].upper()} | {entry['status']} | {entry['formatted_score']} | {notes} |"
        )
    lines.append("")
    return "
".join(lines) + "
"


def render_badge(status: str) -> str:
    color = "#2e8540" if status == "PASS" else "#c92a2a"
    return (
        "<svg xmlns="http://www.w3.org/2000/svg" width="200" height="40">"
        f"<rect width="200" height="40" fill="{color}" rx="6"/>"
        f"<text x="100" y="25" text-anchor="middle" fill="#ffffff" font-size="20""
        " font-family="Helvetica,Arial,sans-serif">Q1 {status}</text>"
        "</svg>"
    )


def render_dag(stages: List[Dict[str, object]]) -> str:
    width = 140 * len(stages)
    height = 120
    svg = [
        f"<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}">",
        "<style>text{font-family:Helvetica,Arial,sans-serif;font-size:14px;}</style>",
        "<defs><marker id="arrow" markerWidth="10" markerHeight="7" refX="10" refY="3.5" orient="auto"><polygon points="0 0, 10 3.5, 0 7" fill="#1f2933"/></marker></defs>",
    ]
    for index, stage in enumerate(stages):
        cx = 70 + index * 140
        status_color = "#2e8540" if stage["status"] == "PASS" else "#c92a2a"
        svg.append(f"<circle cx="{cx}" cy="50" r="32" fill="{status_color}" />")
        svg.append(f"<text x="{cx}" y="55" text-anchor="middle" fill="#ffffff">{stage['stage'].upper()}</text>")
        if index < len(stages) - 1:
            next_cx = 70 + (index + 1) * 140
            svg.append(
                f"<line x1="{cx + 32}" y1="50" x2="{next_cx - 32}" y2="50" stroke="#1f2933" stroke-width="2" marker-end="url(#arrow)" />"
            )
    svg.append("</svg>")
    return "".join(svg)


def render_pr_comment(
    report: Dict[str, object],
    stages: List[Dict[str, object]],
    summary: Dict[str, object],
    bundle_sha256: str,
) -> str:
    emoji = "✅" if report["status"] == "PASS" else "❌"
    lines = [f"{emoji} [Q1 Boss Final report](./report.md)"]
    lines.append("")
    lines.append("![Status](./badge.svg)")
    lines.append("")
    lines.append("## Resumo")
    lines.append(f"- Status global: **{report['status']}**")
    lines.append(f"- Aggregate ratio: {summary['aggregate_ratio']}")
    lines.append(f"- Failing stages: {summary['failing_stages']}")
    lines.append("")
    lines.append("## O que fazer agora")
    failing = [entry for entry in stages if entry["status"] != "PASS"]
    if failing:
        for entry in failing:
            action = entry.get("on_fail", "Ação corretiva pendente.")
            lines.append(f"- {entry['stage'].upper()}: {action}")
    else:
        lines.append("- Nenhuma ação pendente. Continuar monitoramento diário.")
    lines.append("")
    lines.append(f"Bundle SHA-256: `{bundle_sha256}`")
    lines.append("")
    lines.append("Relatório completo disponível em [report.md](./report.md).")
    return "
".join(lines) + "
"


def _serialise_stages_for_hash(stages: List[Dict[str, object]]) -> str:
    serialisable: List[Dict[str, object]] = []
    for entry in stages:
        item = {
            "stage": entry["stage"],
            "status": entry["status"],
            "score": f"{entry['score']}",
            "formatted_score": entry["formatted_score"],
            "generated_at": entry["generated_at"],
        }
        for key in ("notes", "on_fail", "report_path", "bundle_sha256"):
            if key in entry:
                item[key] = entry[key]
        serialisable.append(item)
    serialisable.sort(key=lambda item: item["stage"])
    return json.dumps(serialisable, sort_keys=True, ensure_ascii=False, separators=(",", ":"))


def write_outputs(
    report: Dict[str, object],
    stages: List[Dict[str, object]],
    summary: Dict[str, object],
    bundle_sha256: str,
) -> None:
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)
    (OUTPUT_DIR / "report.json").write_text(
        json.dumps(report, indent=2, ensure_ascii=False) + "
",
        encoding="utf-8",
    )
    markdown = render_markdown(report, stages, summary, bundle_sha256)
    (OUTPUT_DIR / "report.md").write_text(markdown, encoding="utf-8")
    (OUTPUT_DIR / "badge.svg").write_text(render_badge(report["status"]) + "
", encoding="utf-8")
    (OUTPUT_DIR / "dag.svg").write_text(render_dag(stages) + "
", encoding="utf-8")
    pr_comment = render_pr_comment(report, stages, summary, bundle_sha256)
    (OUTPUT_DIR / "pr_comment.md").write_text(pr_comment, encoding="utf-8")
    (OUTPUT_DIR / "bundle.sha256").write_text(bundle_sha256 + "
", encoding="utf-8")
    (OUTPUT_DIR / "guard_status.txt").write_text(report["status"] + "
", encoding="utf-8")


def generate_report() -> BossArtifacts:
    try:
        stages = load_all_stages()
    except AggregationFailure:
        OUTPUT_DIR.mkdir(parents=True, exist_ok=True)
        (OUTPUT_DIR / "guard_status.txt").write_text("FAIL
", encoding="utf-8")
        raise
    summary = compute_summary(stages)
    report = build_report(stages, summary)
    bundle_payload = _serialise_stages_for_hash(stages)
    bundle_sha = sha256(bundle_payload.encode("utf-8")).hexdigest()
    report_with_bundle = dict(report)
    report_with_bundle["bundle"] = {"sha256": bundle_sha}
    write_outputs(report_with_bundle, stages, summary, bundle_sha)
    return BossArtifacts(report=report_with_bundle, stages=stages, summary=summary, bundle_sha256=bundle_sha)


def main() -> int:
    try:
        artifacts = generate_report()
    except AggregationFailure as exc:
        OUTPUT_DIR.mkdir(parents=True, exist_ok=True)
        (OUTPUT_DIR / "guard_status.txt").write_text("FAIL
", encoding="utf-8")
        print(f"FAIL {ERROR_PREFIX}-{exc.code}:{exc.message}")
        return 1
    else:
        print(f"{artifacts.summary['status']} Q1 Boss Final")
        return 0


if __name__ == "__main__":
    raise SystemExit(main())
