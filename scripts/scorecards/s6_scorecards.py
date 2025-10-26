#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import json
import sys
from dataclasses import dataclass
from datetime import datetime, timezone
from decimal import Decimal, ROUND_HALF_EVEN, getcontext
from pathlib import Path
from typing import Dict, Iterable, List, Tuple

BASE_DIR = Path(__file__).resolve().parents[2]
if str(BASE_DIR) not in sys.path:
    sys.path.append(str(BASE_DIR))

import jsonschema
THRESHOLD_PATH = BASE_DIR / "s6_validation" / "thresholds.json"
METRICS_PATH = BASE_DIR / "s6_validation" / "metrics_static.json"
SCHEMAS_DIR = BASE_DIR / "schemas"
OUTPUT_DIR = BASE_DIR / "out" / "s6_scorecards"
ERROR_PREFIX = "S6"

CONTEXT = getcontext()
CONTEXT.prec = 28
CONTEXT.rounding = ROUND_HALF_EVEN
EPSILON = Decimal("1e-12")

SCHEMA_FILES = {
    "thresholds": SCHEMAS_DIR / "thresholds.schema.json",
    "metrics": SCHEMAS_DIR / "metrics.schema.json",
    "report": SCHEMAS_DIR / "report.schema.json",
}

METRIC_ORDER: Tuple[str, ...] = (
    "quorum_ratio",
    "failover_time_p95_s",
    "staleness_p95_s",
    "cdc_lag_p95_s",
    "divergence_pct",
)

DISPLAY_NAMES = {
    "quorum_ratio": "Quorum ratio",
    "failover_time_p95_s": "Failover time p95",
    "staleness_p95_s": "Replica staleness p95",
    "cdc_lag_p95_s": "CDC lag p95",
    "divergence_pct": "Oracle divergence",
}


class ScorecardError(RuntimeError):
    def __init__(self, code: str, message: str) -> None:
        super().__init__(f"{code}:{message}")
        self.code = code
        self.message = message


@dataclass(frozen=True)
class Threshold:
    metric_id: str
    target: Decimal
    comparison: str
    unit: str
    description: str
    on_fail: str


@dataclass(frozen=True)
class Measurement:
    metric_id: str
    observed: Decimal
    unit: str
    sample_size: int
    window: str


@dataclass(frozen=True)
class Evaluation:
    metric_id: str
    threshold: Threshold
    measurement: Measurement
    ok: bool
    delta: Decimal


def fail(code: str, message: str) -> None:
    raise ScorecardError(f"{ERROR_PREFIX}-E-{code}", message)


def load_schema(path: Path) -> Dict[str, object]:
    with path.open("r", encoding="utf-8") as handle:
        return json.load(handle)


def load_json(path: Path, schema_key: str) -> Dict[str, object]:
    if not path.exists():
        fail("MISSING", f"Arquivo obrigatório ausente: {path}")
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:  # pragma: no cover - defensive
        fail("INVALID-JSON", f"Falha ao decodificar {path}: {exc}")
    schema = load_schema(SCHEMA_FILES[schema_key])
    try:
        jsonschema.validate(instance=payload, schema=schema)
    except jsonschema.ValidationError as exc:
        fail("SCHEMA", f"Violação de schema em {path}: {exc.message}")
    return payload


def as_decimal(value: object) -> Decimal:
    try:
        return Decimal(str(value))
    except Exception as exc:  # pragma: no cover - defensive
        fail("DECIMAL", f"Valor inválido para Decimal: {value} ({exc})")
        raise


def parse_thresholds(data: Dict[str, object]) -> Dict[str, Threshold]:
    metrics = data.get("metrics", {})
    parsed: Dict[str, Threshold] = {}
    for metric_id in METRIC_ORDER:
        metric = metrics.get(metric_id)
        if metric is None:
            fail("MISSING-THRESHOLD", f"Métrica ausente em thresholds: {metric_id}")
        parsed[metric_id] = Threshold(
            metric_id=metric_id,
            target=as_decimal(metric["target"]),
            comparison=str(metric["comparison"]),
            unit=str(metric["unit"]),
            description=str(metric["description"]),
            on_fail=str(metric["on_fail"]),
        )
    return parsed


def parse_measurements(data: Dict[str, object]) -> Dict[str, Measurement]:
    metrics = data.get("metrics", {})
    parsed: Dict[str, Measurement] = {}
    for metric_id in METRIC_ORDER:
        metric = metrics.get(metric_id)
        if metric is None:
            fail("MISSING-MEASUREMENT", f"Métrica ausente em observações: {metric_id}")
        parsed[metric_id] = Measurement(
            metric_id=metric_id,
            observed=as_decimal(metric["observed"]),
            unit=str(metric["unit"]),
            sample_size=int(metric["sample_size"]),
            window=str(metric["window"]),
        )
    return parsed


def assert_units(thresholds: Dict[str, Threshold], measurements: Dict[str, Measurement]) -> None:
    for metric_id in METRIC_ORDER:
        threshold = thresholds[metric_id]
        measurement = measurements[metric_id]
        if threshold.unit != measurement.unit:
            fail(
                "UNIT-MISMATCH",
                f"Unidade divergente para {metric_id}: {measurement.unit} != {threshold.unit}",
            )


def compare(threshold: Threshold, measurement: Measurement) -> Tuple[bool, Decimal]:
    value = measurement.observed
    target = threshold.target
    if threshold.comparison == "gte":
        delta = value - target
        ok = value + EPSILON >= target
    elif threshold.comparison == "lte":
        delta = target - value
        ok = value - EPSILON <= target
    else:
        fail("COMPARISON", f"Operador desconhecido: {threshold.comparison}")
        ok = False
        delta = Decimal("0")
    return ok, delta


def evaluate(thresholds: Dict[str, Threshold], measurements: Dict[str, Measurement]) -> List[Evaluation]:
    assert_units(thresholds, measurements)
    evaluations: List[Evaluation] = []
    for metric_id in METRIC_ORDER:
        threshold = thresholds[metric_id]
        measurement = measurements[metric_id]
        ok, delta = compare(threshold, measurement)
        evaluations.append(
            Evaluation(
                metric_id=metric_id,
                threshold=threshold,
                measurement=measurement,
                ok=ok,
                delta=delta,
            )
        )
    return evaluations


def format_value(value: Decimal, unit: str) -> str:
    if unit == "percent":
        return f"{value.quantize(Decimal('0.1'))}%"
    if unit == "ratio":
        return f"{value.quantize(Decimal('0.0001'))}"
    if unit == "seconds":
        return f"{value.quantize(Decimal('0.001'))}s"
    return str(value)


def compute_summary(evaluations: Iterable[Evaluation]) -> Dict[str, int]:
    total = 0
    passing = 0
    for evaluation in evaluations:
        total += 1
        if evaluation.ok:
            passing += 1
    failing = total - passing
    return {"total": total, "passing": passing, "failing": failing}


def compute_bundle_hash(thresholds: Dict[str, object], measurements: Dict[str, object]) -> str:
    thresholds_blob = json.dumps(thresholds, sort_keys=True, ensure_ascii=False, separators=(",", ":"))
    metrics_blob = json.dumps(measurements, sort_keys=True, ensure_ascii=False, separators=(",", ":"))
    material = (thresholds_blob + "\n" + metrics_blob + "\n").encode("utf-8")
    return hashlib.sha256(material).hexdigest()


def build_report(
    evaluations: List[Evaluation],
    generated_at: str,
    thresholds_raw: Dict[str, object],
    metrics_raw: Dict[str, object],
) -> Dict[str, object]:
    summary = compute_summary(evaluations)
    status = "PASS" if summary["failing"] == 0 else "FAIL"
    metrics_block: Dict[str, Dict[str, object]] = {}
    for evaluation in evaluations:
        metric_id = evaluation.metric_id
        measurement = evaluation.measurement
        threshold = evaluation.threshold
        metrics_block[metric_id] = {
            "observed": str(measurement.observed),
            "target": str(threshold.target),
            "delta": str(evaluation.delta),
            "comparison": threshold.comparison,
            "unit": threshold.unit,
            "sample_size": measurement.sample_size,
            "window": measurement.window,
            "ok": evaluation.ok,
            "formatted_observed": format_value(measurement.observed, threshold.unit),
            "formatted_target": format_value(threshold.target, threshold.unit),
            "guidance": threshold.on_fail,
        }
    return {
        "schema_version": 1,
        "timestamp_utc": generated_at,
        "status": status,
        "summary": summary,
        "metrics": metrics_block,
        "bundle_sha256": compute_bundle_hash(thresholds_raw, metrics_raw),
    }


def ensure_output_dir(path: Path) -> None:
    path.mkdir(parents=True, exist_ok=True)


def write_file(path: Path, content: str) -> None:
    path.write_text(content, encoding="utf-8")


def render_markdown(report: Dict[str, object]) -> str:
    lines = ["# Sprint 6 Scorecards", ""]
    emoji = "✅" if report["status"] == "PASS" else "❌"
    lines.append(f"{emoji} Status geral: **{report['status']}**")
    lines.append("")
    lines.append("| Métrica | Valor | Limite | Status | Janela | Amostras |")
    lines.append("| --- | --- | --- | --- | --- | --- |")
    metrics = report["metrics"]
    for metric_id in METRIC_ORDER:
        entry = metrics[metric_id]
        display = DISPLAY_NAMES.get(metric_id, metric_id)
        status_icon = "✅" if entry["ok"] else "❌"
        lines.append(
            f"| {display} | {entry['formatted_observed']} | {entry['formatted_target']} | {status_icon} | "
            f"{entry['window']} | {entry['sample_size']} |"
        )
    lines.append("")
    lines.append("## O que fazer agora")
    failing = [metrics[m] for m in METRIC_ORDER if not metrics[m]["ok"]]
    if failing:
        for metric_id in METRIC_ORDER:
            entry = metrics[metric_id]
            if entry["ok"]:
                continue
            display = DISPLAY_NAMES.get(metric_id, metric_id)
            lines.append(f"- {display}: {entry['guidance']}")
    else:
        lines.append("- Todas as métricas atendidas. Continuar monitoramento e revisar novamente em 24h.")
    lines.append("")
    lines.append("## Metadados")
    lines.append(f"- Gerado em: {report['timestamp_utc']}")
    lines.append(f"- SHA do bundle: `{report['bundle_sha256']}`")
    return "\n".join(lines) + "\n"


def build_pr_comment(report: Dict[str, object]) -> str:
    emoji = "✅" if report["status"] == "PASS" else "❌"
    lines = [f"{emoji} [Sprint 6 report](./report.md)"]
    lines.append("")
    lines.append("![Status](./badge.svg)")
    lines.append("")
    lines.append("## O que fazer agora")
    metrics = report["metrics"]
    failing = [metric_id for metric_id in METRIC_ORDER if not metrics[metric_id]["ok"]]
    if failing:
        for metric_id in failing:
            entry = metrics[metric_id]
            display = DISPLAY_NAMES.get(metric_id, metric_id)
            lines.append(f"- {display}: {entry['guidance']}")
    else:
        lines.append("- Nenhuma ação imediata necessária.")
    lines.append("")
    lines.append("Relatório completo disponível em [report.md](./report.md).")
    return "\n".join(lines) + "\n"


def render_svg_badge(report: Dict[str, object]) -> str:
    status = report["status"]
    color = "#2e8540" if status == "PASS" else "#c92a2a"
    return (
        "<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"160\" height=\"40\">"
        f"<rect width=\"160\" height=\"40\" fill=\"{color}\" rx=\"6\"/>"
        "<text x=\"80\" y=\"25\" text-anchor=\"middle\" fill=\"#ffffff\" font-size=\"20\""
        " font-family=\"Helvetica,Arial,sans-serif\">S6 {status}</text>"
        "</svg>"
    )


def render_scorecard_svg(report: Dict[str, object]) -> str:
    metrics = report["metrics"]
    rows = len(METRIC_ORDER)
    height = 60 + 30 * rows
    svg_parts = [
        f"<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"520\" height=\"{height}\">",
        "<style>text{font-family:Helvetica,Arial,sans-serif;font-size:14px;}</style>",
        f"<rect width=\"520\" height=\"{height}\" fill=\"#ffffff\" stroke=\"#1f2933\" rx=\"8\"/>",
        "<text x=\"20\" y=\"30\" font-size=\"18\" font-weight=\"bold\">Sprint 6 Scorecards</text>",
    ]
    y = 60
    for metric_id in METRIC_ORDER:
        entry = metrics[metric_id]
        display = DISPLAY_NAMES.get(metric_id, metric_id)
        status_color = "#2e8540" if entry["ok"] else "#c92a2a"
        status_text = "PASS" if entry["ok"] else "FAIL"
        svg_parts.append(
            f"<text x=\"20\" y=\"{y}\">{display}</text>"
            f"<text x=\"260\" y=\"{y}\">{entry['formatted_observed']}</text>"
            f"<text x=\"360\" y=\"{y}\">{entry['formatted_target']}</text>"
            f"<text x=\"460\" y=\"{y}\" fill=\"{status_color}\">{status_text}</text>"
        )
        y += 30
    svg_parts.append("</svg>")
    return "".join(svg_parts)


def write_outputs(report: Dict[str, object]) -> None:
    ensure_output_dir(OUTPUT_DIR)
    write_file(OUTPUT_DIR / "report.json", json.dumps(report, indent=2, ensure_ascii=False) + "\n")
    write_file(OUTPUT_DIR / "report.md", render_markdown(report))
    write_file(OUTPUT_DIR / "pr_comment.md", build_pr_comment(report))
    write_file(OUTPUT_DIR / "badge.svg", render_svg_badge(report) + "\n")
    write_file(OUTPUT_DIR / "scorecard.svg", render_scorecard_svg(report) + "\n")
    write_file(OUTPUT_DIR / "guard_status.txt", (report["status"] + "\n"))
    write_file(OUTPUT_DIR / "bundle.sha256", report["bundle_sha256"] + "\n")


def generate_report(
    threshold_path: Path = THRESHOLD_PATH,
    metrics_path: Path = METRICS_PATH,
) -> Dict[str, object]:
    thresholds_raw = load_json(threshold_path, "thresholds")
    metrics_raw = load_json(metrics_path, "metrics")
    thresholds = parse_thresholds(thresholds_raw)
    measurements = parse_measurements(metrics_raw)
    evaluations = evaluate(thresholds, measurements)
    generated_at = datetime.now(timezone.utc).replace(microsecond=0).isoformat()
    report = build_report(evaluations, generated_at, thresholds_raw, metrics_raw)
    jsonschema.validate(instance=report, schema=load_schema(SCHEMA_FILES["report"]))
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
