#!/usr/bin/env python3
from __future__ import annotations

import json
import hashlib
import sys
from dataclasses import dataclass
from datetime import datetime, timezone
from decimal import Decimal, getcontext, ROUND_HALF_EVEN
from pathlib import Path
from typing import Dict, Iterable, List, Tuple

BASE_DIR = Path(__file__).resolve().parents[2]
sys.path.append(str(BASE_DIR))

import jsonschema

CONTEXT = getcontext()
CONTEXT.prec = 28
CONTEXT.rounding = ROUND_HALF_EVEN

EPSILON = Decimal("1e-12")
THRESHOLD_PATH = BASE_DIR / "s6_validation" / "thresholds.json"
METRICS_PATH = BASE_DIR / "s6_validation" / "metrics_static.json"
SCHEMAS_DIR = BASE_DIR / "schemas"
OUTPUT_DIR = BASE_DIR / "out" / "s6_scorecards"
ERROR_PREFIX = "S6"


class ScorecardError(RuntimeError):
    def __init__(self, code: str, message: str) -> None:
        super().__init__(f"{code}:{message}")
        self.code = code
        self.message = message


@dataclass(frozen=True)
class Threshold:
    metric_id: str
    order: int
    display_name: str
    comparison: str
    target_value: Decimal
    unit: str
    description: str
    on_fail: str


@dataclass(frozen=True)
class Measurement:
    metric_id: str
    value: Decimal
    unit: str
    sample_size: int
    measurement: str


@dataclass(frozen=True)
class Evaluation:
    threshold: Threshold
    measurement: Measurement
    status: str
    delta: Decimal


SCHEMA_FILES = {
    "thresholds": SCHEMAS_DIR / "thresholds.schema.json",
    "metrics": SCHEMAS_DIR / "metrics.schema.json",
    "report": SCHEMAS_DIR / "report.schema.json",
}


def fail(code: str, message: str) -> None:
    raise ScorecardError(f"{ERROR_PREFIX}-E-{code}", message)


def load_json(path: Path, schema_key: str) -> Dict:
    if not path.exists():
        fail("MISSING", f"Arquivo obrigatório ausente: {path}")
    try:
        content = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        fail("INVALID-JSON", f"Falha ao decodificar {path}: {exc}")
    schema_path = SCHEMA_FILES[schema_key]
    with schema_path.open("r", encoding="utf-8") as handle:
        schema = json.load(handle)
    try:
        jsonschema.validate(instance=content, schema=schema)
    except jsonschema.ValidationError as exc:
        fail("SCHEMA", f"Violação de schema em {path}: {exc.message}")
    return content


def decimal_from(value: str) -> Decimal:
    try:
        return Decimal(value)
    except Exception as exc:  # pragma: no cover
        fail("DECIMAL", f"Valor inválido para Decimal: {value} ({exc})")
        raise


def parse_thresholds(data: Dict) -> List[Threshold]:
    thresholds: List[Threshold] = []
    seen_ids: set[str] = set()
    for entry in data.get("metrics", []):
        metric_id = entry["id"]
        if metric_id in seen_ids:
            fail("DUPLICATE-TH", f"Threshold duplicado para {metric_id}")
        seen_ids.add(metric_id)
        thresholds.append(
            Threshold(
                metric_id=metric_id,
                order=int(entry["order"]),
                display_name=entry["display_name"],
                comparison=entry["comparison"],
                target_value=decimal_from(entry["target_value"]),
                unit=entry["unit"],
                description=entry["description"],
                on_fail=entry["on_fail"],
            )
        )
    thresholds.sort(key=lambda item: item.order)
    return thresholds


def parse_measurements(data: Dict) -> Dict[str, Measurement]:
    metrics: Dict[str, Measurement] = {}
    for entry in data.get("metrics", []):
        metric_id = entry["id"]
        if metric_id in metrics:
            fail("DUPLICATE-MEASUREMENT", f"Métrica duplicada: {metric_id}")
        metrics[metric_id] = Measurement(
            metric_id=metric_id,
            value=decimal_from(entry["value"]),
            unit=entry["unit"],
            sample_size=int(entry["sample_size"]),
            measurement=entry["measurement"],
        )
    return metrics


def assert_units(thresholds: Iterable[Threshold], measurements: Dict[str, Measurement]) -> None:
    for threshold in thresholds:
        measurement = measurements.get(threshold.metric_id)
        if measurement is None:
            fail("MISSING-METRIC", f"Métrica sem coleta: {threshold.metric_id}")
        if measurement.unit != threshold.unit:
            fail(
                "UNIT-MISMATCH",
                f"Unidade divergente para {threshold.metric_id}: {measurement.unit} != {threshold.unit}",
            )


def compare(threshold: Threshold, measurement: Measurement) -> Tuple[str, Decimal]:
    value = measurement.value
    target = threshold.target_value
    comparison = threshold.comparison
    if comparison == "gte":
        delta = value - target
        status = "pass" if value + EPSILON >= target else "fail"
    elif comparison == "lte":
        delta = target - value
        status = "pass" if value - EPSILON <= target else "fail"
    else:
        fail("COMPARISON", f"Operador desconhecido: {comparison}")
        delta = Decimal("0")
        status = "fail"
    return status, delta


def format_value(value: Decimal, unit: str) -> str:
    if unit == "percent":
        return f"{value.quantize(Decimal('0.1'))}%"
    if unit == "ratio":
        return f"{value.quantize(Decimal('0.0001'))}"
    if unit == "seconds":
        return f"{value.quantize(Decimal('0.001'))}s"
    return str(value)


def evaluate(thresholds: List[Threshold], measurements: Dict[str, Measurement]) -> List[Evaluation]:
    evaluations: List[Evaluation] = []
    assert_units(thresholds, measurements)
    for threshold in thresholds:
        measurement = measurements[threshold.metric_id]
        status, delta = compare(threshold, measurement)
        evaluations.append(
            Evaluation(
                threshold=threshold,
                measurement=measurement,
                status=status,
                delta=delta,
            )
        )
    return evaluations


def make_summary(evaluations: List[Evaluation]) -> Dict[str, object]:
    total = len(evaluations)
    passing = sum(1 for evaluation in evaluations if evaluation.status == "pass")
    failing = total - passing
    status = "pass" if failing == 0 else "fail"
    return {
        "status": status,
        "total_metrics": total,
        "passing": passing,
        "failing": failing,
    }


def ensure_output_dir(path: Path) -> None:
    path.mkdir(parents=True, exist_ok=True)


def write_file(path: Path, content: str) -> None:
    path.write_text(content, encoding="utf-8")


def build_report(evaluations: List[Evaluation], generated_at: str, thresholds_meta: Dict, metrics_meta: Dict) -> Dict[str, object]:
    items: List[Dict[str, object]] = []
    for evaluation in evaluations:
        threshold = evaluation.threshold
        measurement = evaluation.measurement
        items.append(
            {
                "id": threshold.metric_id,
                "display_name": threshold.display_name,
                "status": evaluation.status,
                "comparison": threshold.comparison,
                "value": str(measurement.value),
                "formatted_value": format_value(measurement.value, threshold.unit),
                "threshold_value": str(threshold.target_value),
                "formatted_threshold": format_value(threshold.target_value, threshold.unit),
                "unit": threshold.unit,
                "delta": str(evaluation.delta),
                "sample_size": measurement.sample_size,
                "measurement_window": measurement.measurement,
                "description": threshold.description,
                "on_fail": threshold.on_fail,
            }
        )
    summary = make_summary(evaluations)
    bundle_content = json.dumps(items, sort_keys=True, ensure_ascii=False, separators=(",", ":")).encode("utf-8")
    bundle_hash = hashlib.sha256(bundle_content).hexdigest()
    return {
        "schema_version": 1,
        "generated_at": generated_at,
        "summary": summary,
        "thresholds_version": thresholds_meta.get("schema_version"),
        "metrics_version": metrics_meta.get("schema_version"),
        "metrics_collected_at": metrics_meta.get("collected_at"),
        "items": items,
        "bundle_sha256": bundle_hash,
    }


def render_markdown(report: Dict[str, object]) -> str:
    lines = ["# Sprint 6 Scorecards", ""]
    summary = report["summary"]
    status_emoji = "✅" if summary["status"] == "pass" else "❌"
    lines.append(f"{status_emoji} Status geral: **{summary['status'].upper()}**")
    lines.append("")
    lines.append("| Métrica | Valor | Limite | Status | Janela | Amostras |")
    lines.append("| --- | --- | --- | --- | --- | --- |")
    for item in report["items"]:
        status = "✅" if item["status"] == "pass" else "❌"
        lines.append(
            f"| {item['display_name']} | {item['formatted_value']} | {item['formatted_threshold']} | {status} | "
            f"{item['measurement_window']} | {item['sample_size']} |"
        )
    lines.append("")
    lines.append("## O que fazer agora")
    failing = [item for item in report["items"] if item["status"] != "pass"]
    if failing:
        for item in failing:
            lines.append(f"- {item['display_name']}: {item['on_fail']}")
    else:
        lines.append("- Todas as métricas atendidas. Continuar monitoramento e revisar novamente em 24h.")
    lines.append("")
    lines.append("## Metadados")
    lines.append(f"- Gerado em: {report['generated_at']}")
    lines.append(f"- SHA do bundle: `{report['bundle_sha256']}`")
    return "\n".join(lines) + "\n"


def build_pr_comment(report: Dict[str, object]) -> str:
    summary = report["summary"]
    badge_line = "✅" if summary["status"] == "pass" else "❌"
    badge_line += " [Sprint 6 report](./report.md)"
    lines = [badge_line]
    lines.append("")
    lines.append("![Status](./badge.svg)")
    lines.append("")
    lines.append("## O que fazer agora")
    failing = [item for item in report["items"] if item["status"] != "pass"]
    if failing:
        for item in failing:
            lines.append(f"- {item['display_name']}: {item['on_fail']}")
    else:
        lines.append("- Nenhuma ação imediata necessária.")
    lines.append("")
    lines.append("Relatório completo disponível em [report.md](./report.md).")
    return "\n".join(lines) + "\n"


def render_svg_badge(report: Dict[str, object]) -> str:
    status = report["summary"]["status"]
    label_color = "#2e8540" if status == "pass" else "#c92a2a"
    status_text = "PASS" if status == "pass" else "FAIL"
    return (
        "<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"160\" height=\"40\">"
        f"<rect width=\"160\" height=\"40\" fill=\"{label_color}\" rx=\"6\"/>"
        "<text x=\"80\" y=\"25\" text-anchor=\"middle\" fill=\"#ffffff\" font-size=\"20\""
        " font-family=\"Helvetica,Arial,sans-serif\">S6 {status}</text>".format(status=status_text)
        + "</svg>"
    )


def render_scorecard_svg(report: Dict[str, object]) -> str:
    rows = len(report["items"])
    height = 60 + 30 * rows
    header = (
        f"<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"520\" height=\"{height}\">"
        "<style>text{font-family:Helvetica,Arial,sans-serif;font-size:14px;}</style>"
        "<rect width=\"520\" height=\"{height}\" fill=\"#ffffff\" stroke=\"#1f2933\" rx=\"8\"/>"
        "<text x=\"20\" y=\"30\" font-size=\"18\" font-weight=\"bold\">Sprint 6 Scorecards</text>"
    )
    lines = [header]
    y = 60
    for item in report["items"]:
        status_color = "#2e8540" if item["status"] == "pass" else "#c92a2a"
        status_text = "PASS" if item["status"] == "pass" else "FAIL"
        lines.append(
            f"<text x=\"20\" y=\"{y}\">{item['display_name']}</text>"
            f"<text x=\"260\" y=\"{y}\">{item['formatted_value']}</text>"
            f"<text x=\"360\" y=\"{y}\">{item['formatted_threshold']}</text>"
            f"<text x=\"460\" y=\"{y}\" fill=\"{status_color}\">{status_text}</text>"
        )
        y += 30
    lines.append("</svg>")
    return "".join(lines)


def write_outputs(report: Dict[str, object]) -> None:
    ensure_output_dir(OUTPUT_DIR)
    write_file(OUTPUT_DIR / "report.json", json.dumps(report, indent=2, ensure_ascii=False) + "\n")
    markdown = render_markdown(report)
    write_file(OUTPUT_DIR / "report.md", markdown)
    write_file(OUTPUT_DIR / "pr_comment.md", build_pr_comment(report))
    badge_svg = render_svg_badge(report)
    write_file(OUTPUT_DIR / "badge.svg", badge_svg + "\n")
    scorecard_svg = render_scorecard_svg(report)
    write_file(OUTPUT_DIR / "scorecard.svg", scorecard_svg + "\n")
    write_file(OUTPUT_DIR / "guard_status.txt", ("PASS" if report["summary"]["status"] == "pass" else "FAIL") + "\n")
    write_file(OUTPUT_DIR / "bundle.sha256", report["bundle_sha256"] + "\n")


def generate_report(threshold_path: Path = THRESHOLD_PATH, metrics_path: Path = METRICS_PATH) -> Dict[str, object]:
    thresholds_raw = load_json(threshold_path, "thresholds")
    metrics_raw = load_json(metrics_path, "metrics")
    thresholds = parse_thresholds(thresholds_raw)
    measurements = parse_measurements(metrics_raw)
    evaluations = evaluate(thresholds, measurements)
    generated_at = datetime.now(timezone.utc).replace(microsecond=0).isoformat()
    report = build_report(evaluations, generated_at, thresholds_raw, metrics_raw)
    write_outputs(report)
    return report


def main() -> int:
    try:
        report = generate_report()
    except ScorecardError as exc:
        print(f"FAIL {exc}")
        ensure_output_dir(OUTPUT_DIR)
        write_file(OUTPUT_DIR / "guard_status.txt", "FAIL\n")
        return 1
    else:
        print("PASS Sprint 6 scorecards")
        return 0


if __name__ == "__main__":
    raise SystemExit(main())
