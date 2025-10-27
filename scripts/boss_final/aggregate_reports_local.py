from __future__ import annotations

import hashlib
import json
import os
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Dict, Iterable, List, Tuple

SCHEMA = "trendmarketv2.q1.boss.report"
SCHEMA_VERSION = 2
STAGES = tuple(f"s{i}" for i in range(1, 7))
VARIANTS = ("primary", "clean")


@dataclass
class VariantResult:
    status: str
    notes: str
    timestamp: str


@dataclass
class StageAggregate:
    status: str
    notes: str
    variants: Dict[str, VariantResult]


def _iso_utc() -> str:
    return (
        datetime.now(timezone.utc)
        .replace(microsecond=0)
        .isoformat()
        .replace("+00:00", "Z")
    )


def _canonical(payload: Dict[str, object]) -> str:
    return json.dumps(payload, sort_keys=True, ensure_ascii=False, separators=(",", ":"))


def _normalize_status(raw: object) -> str:
    if isinstance(raw, str):
        value = raw.strip().lower()
        if value in {"pass", "passed", "success", "ok"}:
            return "PASS"
        if value in {"fail", "failed", "failure", "error"}:
            return "FAIL"
    return "FAIL"


def _load_stage_entries(arts_dir: Path) -> Iterable[Tuple[Dict[str, object], Path]]:
    for report_path in arts_dir.rglob("report.json"):
        try:
            payload = json.loads(report_path.read_text(encoding="utf-8"))
        except Exception as exc:  # noqa: BLE001
            yield (
                {
                    "name": report_path.parent.name,
                    "status": "failed",
                    "exit_code": None,
                    "notes": f"invalid report.json: {exc}",
                },
                report_path.parent,
            )
            continue
        entries = payload.get("stages") if isinstance(payload, dict) else None
        if not isinstance(entries, list):
            continue
        for entry in entries:
            if not isinstance(entry, dict):
                continue
            yield entry, report_path.parent


def _tail_non_empty(path: Path, limit: int = 50) -> str:
    if not path.exists():
        return ""
    try:
        lines = path.read_text(encoding="utf-8", errors="ignore").splitlines()
    except Exception:  # noqa: BLE001
        return ""
    for line in reversed(lines[-limit:]):
        if line.strip():
            return line.strip()
    return ""


def _default_variant(status: str, note: str, timestamp: str) -> VariantResult:
    return VariantResult(status=status, notes=note, timestamp=timestamp)


def aggregate_reports(arts_dir: Path, report_dir: Path) -> Dict[str, object]:
    report_dir.mkdir(parents=True, exist_ok=True)
    now = _iso_utc()
    stage_data: Dict[str, Dict[str, VariantResult]] = {stage: {} for stage in STAGES}
    stage_notes: Dict[str, List[str]] = {stage: [] for stage in STAGES}

    for entry, parent in _load_stage_entries(arts_dir):
        stage_name = str(entry.get("name", "")).strip().lower()
        if stage_name not in stage_data:
            continue
        variant = "clean" if bool(entry.get("clean")) else entry.get("variant", "primary")
        if variant not in VARIANTS:
            variant = "primary"
        status = _normalize_status(entry.get("status"))
        exit_code = entry.get("exit_code")
        timestamp = str(entry.get("timestamp_utc") or entry.get("generated_at") or now)
        note = str(entry.get("notes") or "").strip()
        if not note:
            if status == "PASS":
                note = "Guard finalizado com sucesso"
            elif exit_code is not None:
                note = f"Guard falhou (exit {exit_code})"
            else:
                note = "Guard falhou"
        if status != "PASS":
            excerpt = _tail_non_empty(parent / "guard.log")
            if excerpt:
                note = f"{note} — {excerpt}"
        stage_data[stage_name][variant] = VariantResult(
            status=status,
            notes=note,
            timestamp=timestamp,
        )
        stage_notes[stage_name].append(f"{variant}:{status}")

    for stage in STAGES:
        variants = stage_data[stage]
        for variant in VARIANTS:
            if variant not in variants:
                variants[variant] = _default_variant(
                    status="FAIL",
                    note="Dados do variant ausentes (artifact não encontrado)",
                    timestamp=now,
                )
                stage_notes[stage].append(f"{variant}:FAIL")

    stage_summaries: Dict[str, StageAggregate] = {}
    for stage in STAGES:
        variants = stage_data[stage]
        status = "PASS" if all(v.status == "PASS" for v in variants.values()) else "FAIL"
        notes = " | ".join(stage_notes[stage]) if stage_notes[stage] else status
        stage_summaries[stage] = StageAggregate(status=status, notes=notes, variants=variants)

    bundle_pieces: List[str] = []
    for stage in STAGES:
        aggregate = stage_summaries[stage]
        bundle_pieces.append(
            _canonical({"stage": stage, "status": aggregate.status, "notes": aggregate.notes}) + "\n"
        )
        for variant in VARIANTS:
            result = aggregate.variants[variant]
            bundle_pieces.append(
                _canonical(
                    {
                        "stage": stage,
                        "variant": variant,
                        "status": result.status,
                        "notes": result.notes,
                        "timestamp_utc": result.timestamp,
                    }
                )
                + "\n"
            )
    bundle_sha = hashlib.sha256("".join(bundle_pieces).encode("utf-8")).hexdigest()

    overall_status = "PASS" if all(
        aggregate.status == "PASS" for aggregate in stage_summaries.values()
    ) else "FAIL"

    report = {
        "schema": SCHEMA,
        "schema_version": SCHEMA_VERSION,
        "timestamp_utc": now,
        "status": overall_status,
        "stages": {
            stage: {
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
            for stage, aggregate in stage_summaries.items()
        },
        "bundle": {"sha256": bundle_sha},
    }

    (report_dir / "report.json").write_text(
        json.dumps(report, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )
    (report_dir / "guard_status.txt").write_text(f"{overall_status}\n", encoding="utf-8")

    table_lines = ["# Q1 Boss Final (local)", "", f"Status geral: **{overall_status}**", ""]
    table_lines.append("| Estágio | Status | Notas |")
    table_lines.append("| --- | --- | --- |")
    for stage in STAGES:
        aggregate = stage_summaries[stage]
        table_lines.append(
            f"| {stage.upper()} | {aggregate.status} | {aggregate.notes} |"
        )
    (report_dir / "report.md").write_text("\n".join(table_lines) + "\n", encoding="utf-8")

    comment_lines = [
        f"{'✅' if overall_status == 'PASS' else '❌'} Q1 Boss Final",
        "",
        "Resumo por estágio:",
    ]
    for stage in STAGES:
        aggregate = stage_summaries[stage]
        icon = "✅" if aggregate.status == "PASS" else "❌"
        comment_lines.append(f"- {icon} {stage.upper()}: {aggregate.notes}")
    (report_dir / "pr_comment.md").write_text("\n".join(comment_lines) + "\n", encoding="utf-8")

    dag_lines = [
        '<svg xmlns="http://www.w3.org/2000/svg" width="840" height="120">',
        '<style>text{font-family:Helvetica,Arial,sans-serif;font-size:14px;}line{stroke:#1f2933;stroke-width:2;}</style>',
        '<defs><marker id="arrow" markerWidth="10" markerHeight="7" refX="10" refY="3.5" orient="auto"><polygon points="0 0, 10 3.5, 0 7" fill="#1f2933"/></marker></defs>',
    ]
    for index, stage in enumerate(STAGES):
        aggregate = stage_summaries[stage]
        x = 70 + index * 130
        color = "#2e8540" if aggregate.status == "PASS" else "#c92a2a"
        dag_lines.append(f'<circle cx="{x}" cy="50" r="30" fill="{color}" />')
        dag_lines.append(
            f'<text x="{x}" y="55" text-anchor="middle" fill="#ffffff">{stage.upper()}</text>'
        )
        if index < len(STAGES) - 1:
            next_x = 70 + (index + 1) * 130
            dag_lines.append(
                f'<line x1="{x + 30}" y1="50" x2="{next_x - 30}" y2="50" marker-end="url(#arrow)"/>'
            )
    dag_lines.append("</svg>")
    (report_dir / "dag.svg").write_text("".join(dag_lines) + "\n", encoding="utf-8")

    summary = {
        "status": overall_status,
        "stages": {stage: aggregate.status for stage, aggregate in stage_summaries.items()},
    }
    print(json.dumps(summary, ensure_ascii=False))
    return report


def main() -> int:
    arts_dir = Path(os.environ.get("ARTS_DIR") or Path(os.environ.get("RUNNER_TEMP", ".")) / "boss-arts")
    report_dir = Path(os.environ.get("REPORT_DIR") or Path(os.environ.get("RUNNER_TEMP", ".")) / "boss-aggregate")
    report = aggregate_reports(arts_dir, report_dir)
    return 0 if report["status"] == "PASS" else 1


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
