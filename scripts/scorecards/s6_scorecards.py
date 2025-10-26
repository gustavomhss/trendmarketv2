#!/usr/bin/env python3
"""Sprint 6 scorecard generator."""

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
from typing import Any, Dict, Iterable, List

BASE_DIR = Path(__file__).resolve().parents[2]
if str(BASE_DIR) not in sys.path:
    sys.path.insert(0, str(BASE_DIR))

import jsonschema
from jsonschema import Draft7Validator

SCHEMAS_DIR = BASE_DIR / "schemas"
THRESHOLDS_PATH = BASE_DIR / "s6_validation" / "thresholds.json"
METRICS_PATH = BASE_DIR / "s6_validation" / "metrics_static.json"
OUTPUT_DIR = BASE_DIR / "out" / "s6_scorecards"

SCHEMA_FILES: Dict[str, Path] = {
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
SCHEMA_VERSION = 2
REPORT_SCHEMA = "trendmarketv2.sprint6.report"
ERROR_PREFIX = "S6"
EPSILON = Decimal("1e-12")

getcontext().prec = 28
getcontext().rounding = ROUND_HALF_EVEN

_FORMAT_CHECKER = jsonschema.FormatChecker()
_VALIDATORS: Dict[str, Draft7Validator] = {}


class ScorecardError(RuntimeError):
    """Exception raised for deterministic scorecard failures."""

    def __init__(self, code: str, message: str) -> None:
        self.code = f"{ERROR_PREFIX}-E-{code}"
        super().__init__(f"{self.code}:{message}")


def fail(code: str, message: str) -> None:
    raise ScorecardError(code, message)


@dataclass(frozen=True)
class MetricDefinition:
    key: str
    label: str
    comparator: str
    unit: str
    quantize: Decimal


@dataclass(frozen=True)
class MetricResult:
    definition: MetricDefinition
    observed: Decimal
    target: Decimal
    ok: bool

    def formatted_observed(self) -> str:
        return format_value(self.observed.quantize(self.definition.quantize), self.definition.unit)

    def formatted_target(self) -> str:
        return format_value(self.target.quantize(self.definition.quantize), self.definition.unit)

    def status_text(self) -> str:
        return "PASS" if self.ok else "FAIL"


@dataclass(frozen=True)
class ScorecardArtifacts:
    report: Dict[str, Any]
    results: List[MetricResult]
    bundle_sha256: str
    thresholds: Dict[str, Any]
    metrics: Dict[str, Any]


METRIC_DEFINITIONS: List[MetricDefinition] = [
    MetricDefinition(
        key="quorum_ratio",
        label="Quorum Ratio",
        comparator="gte",
        unit="ratio",
        quantize=Decimal("0.0001"),
    ),
    MetricDefinition(
        key="failover_time_p95_s",
        label="Failover p95 (s)",
        comparator="lte",
        unit="seconds",
        quantize=Decimal("0.001"),
    ),
    MetricDefinition(
        key="staleness_p95_s",
        label="Staleness p95 (s)",
        comparator="lte",
        unit="seconds",
        quantize=Decimal("0.001"),
    ),
    MetricDefinition(
        key="cdc_lag_p95_s",
        label="CDC Lag p95 (s)",
        comparator="lte",
        unit="seconds",
        quantize=Decimal("0.001"),
    ),
    MetricDefinition(
        key="divergence_pct",
        label="Divergence (%)",
        comparator="lte",
        unit="percent",
        quantize=Decimal("0.1"),
    ),
]


def _validator_for(schema_key: str) -> Draft7Validator:
    try:
        return _VALIDATORS[schema_key]
    except KeyError:
        schema_path = SCHEMA_FILES[schema_key]
        try:
            schema = json.loads(schema_path.read_text(encoding="utf-8"))
        except FileNotFoundError as exc:  # pragma: no cover - configuration error
            fail("SCHEMA-MISSING", f"Schema ausente: {schema_path}: {exc}")
        validator = Draft7Validator(schema, format_checker=_FORMAT_CHECKER)
        _VALIDATORS[schema_key] = validator
        return validator


def load_json(path: Path, schema_key: str) -> Dict[str, Any]:
    if not path.exists():
        fail("MISSING", f"Arquivo obrigatório ausente: {path}")
    try:
        text = path.read_text(encoding="utf-8")
    except UnicodeDecodeError as exc:
        fail("ENCODING", f"Arquivo não está em UTF-8: {path}: {exc}")
    except OSError as exc:  # pragma: no cover - defensive
        fail("IO", f"Falha ao ler {path}: {exc}")
    try:
        payload = json.loads(text)
    except json.JSONDecodeError as exc:
        fail("INVALID-JSON", f"Falha ao decodificar {path}: {exc}")
    validator = _validator_for(schema_key)
    try:
        validator.validate(payload)
    except jsonschema.ValidationError as exc:
        location = "/".join(str(part) for part in exc.path)
        suffix = f" (campo {location})" if location else ""
        fail("SCHEMA", f"Violação de schema em {path}: {exc.message}{suffix}")
    return payload


def decimal_from(value: Any) -> Decimal:
    if isinstance(value, Decimal):
        return value
    if isinstance(value, (int, float, str)):
        try:
            return Decimal(str(value))
        except Exception as exc:  # pragma: no cover - defensive
            fail("DECIMAL", f"Valor inválido {value!r}: {exc}")
    fail("DECIMAL", f"Valor não numérico: {value!r}")


def compare(observed: Decimal, target: Decimal, comparator: str) -> bool:
    if comparator == "gte":
        return observed + EPSILON >= target
    if comparator == "lte":
        return observed - EPSILON <= target
    fail("COMPARATOR", f"Operador desconhecido: {comparator}")
    return False


def evaluate_metrics(thresholds: Dict[str, Any], metrics: Dict[str, Any]) -> List[MetricResult]:
    results: List[MetricResult] = []
    for definition in METRIC_DEFINITIONS:
        if definition.key not in thresholds:
            fail("MISSING-THRESHOLD", f"Threshold ausente para {definition.key}")
        if definition.key not in metrics:
            fail("MISSING-METRIC", f"Métrica ausente: {definition.key}")
        target = decimal_from(thresholds[definition.key])
        observed = decimal_from(metrics[definition.key])
        ok = compare(observed, target, definition.comparator)
        results.append(
            MetricResult(
                definition=definition,
                observed=observed,
                target=target,
                ok=ok,
            )
        )
    return results


def compute_status(results: Iterable[MetricResult]) -> str:
    return "PASS" if all(result.ok for result in results) else "FAIL"


def isoformat_utc() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def canonical_dumps(data: Dict[str, Any]) -> str:
    return json.dumps(data, sort_keys=True, ensure_ascii=False, separators=(",", ":")) + "\n"


def compute_bundle_sha(thresholds: Dict[str, Any], metrics: Dict[str, Any]) -> str:
    payload = canonical_dumps(thresholds) + canonical_dumps(metrics)
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()


def format_value(value: Decimal, unit: str) -> str:
    if unit == "ratio":
        return f"{value:.4f}"
    if unit == "seconds":
        return f"{value:.3f}s"
    if unit == "percent":
        return f"{value:.1f}%"
    return format(value, "f")


def build_report(
    thresholds: Dict[str, Any],
    metrics: Dict[str, Any],
    results: List[MetricResult],
    bundle_sha: str,
) -> Dict[str, Any]:
    metrics_block = {
        result.definition.key: {
            "observed": float(result.observed),
            "target": float(result.target),
            "ok": bool(result.ok),
        }
        for result in results
    }
    status = compute_status(results)
    report = {
        "schema": REPORT_SCHEMA,
        "schema_version": SCHEMA_VERSION,
        "timestamp_utc": isoformat_utc(),
        "status": status,
        "metrics": metrics_block,
        "inputs": {
            "thresholds": {
                "schema": thresholds.get("schema"),
                "schema_version": thresholds.get("schema_version"),
                "timestamp_utc": thresholds.get("timestamp_utc"),
            },
            "metrics": {
                "schema": metrics.get("schema"),
                "schema_version": metrics.get("schema_version"),
                "timestamp_utc": metrics.get("timestamp_utc"),
            },
        },
        "bundle": {"sha256": bundle_sha},
    }
    return report


def render_markdown(artifacts: ScorecardArtifacts) -> str:
    report = artifacts.report
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
    lines.append(f"- Relatório gerado em: {report['timestamp_utc']}")
    lines.append(
        "- Thresholds: "
        f"v{report['inputs']['thresholds']['schema_version']} @ {report['inputs']['thresholds']['timestamp_utc']}"
    )
    lines.append(
        "- Métricas: "
        f"v{report['inputs']['metrics']['schema_version']} @ {report['inputs']['metrics']['timestamp_utc']}"
    )
    lines.append(f"- Bundle SHA-256: `{artifacts.bundle_sha256}`")
    lines.append("")
    lines.append("| Métrica | Observado | Alvo | Status |")
    lines.append("| --- | --- | --- | --- |")
    for result in artifacts.results:
        metric_emoji = "✅" if result.ok else "❌"
        lines.append(
            f"| {result.definition.label} | {result.formatted_observed()} | {result.formatted_target()} | {metric_emoji} {result.status_text()} |"
        )
    lines.append("")
    lines.append("## Próximos passos")
    failing = [result for result in artifacts.results if not result.ok]
    if failing:
        for result in failing:
            lines.append(
                f"- {result.definition.label}: acionar runbook da Sprint 6 para restaurar o indicador."
            )
    else:
        lines.append("- Nenhuma ação imediata necessária; manter monitoramento preventivo.")
    lines.append("")
    lines.append("## Governança")
    lines.append("- Contratos validados contra os schemas Draft-07.")
    lines.append("- Bundle calculado via SHA-256 sobre `thresholds.json` + `metrics_static.json` canônicos.")
    lines.append("")
    return "\n".join(lines) + "\n"


def render_pr_comment(artifacts: ScorecardArtifacts) -> str:
    emoji = "✅" if artifacts.report["status"] == "PASS" else "❌"
    lines = [f"{emoji} [Sprint 6 report](./report.md)", ""]
    lines.append("![Status](./badge.svg)")
    lines.append("")
    for result in artifacts.results:
        metric_emoji = "✅" if result.ok else "❌"
        lines.append(
            f"- {result.definition.label}: {metric_emoji} {result.status_text()}"
        )
    lines.append("")
    lines.append(f"Bundle SHA-256: `{artifacts.bundle_sha256}`")
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
def render_badge(status: str) -> str:
    color = "4c9a2a" if status == "PASS" else "cc3300"
    return (
        "<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"150\" height=\"20\" role=\"img\">"
        "<linearGradient id=\"b\" x2=\"0\" y2=\"100%\"><stop offset=\"0\" stop-color=\"#bbb\" stop-opacity=\".1\"/>"
        "<stop offset=\"1\" stop-opacity=\".1\"/></linearGradient>"
        "<mask id=\"a\"><rect width=\"150\" height=\"20\" rx=\"3\" fill=\"#fff\"/></mask>"
        "<g mask=\"url(#a)\">"
        "<rect width=\"70\" height=\"20\" fill=\"#555\"/>"
        f"<rect x=\"70\" width=\"80\" height=\"20\" fill=\"#{color}\"/>"
        "<rect width=\"150\" height=\"20\" fill=\"url(#b)\"/></g>"
        "<g fill=\"#fff\" text-anchor=\"middle\" font-family=\"DejaVu Sans,Verdana,Geneva,sans-serif\" font-size=\"11\">"
        "<text x=\"35\" y=\"15\">S6</text>"
        f"<text x=\"110\" y=\"15\">{status}</text>"
        "</g></svg>"
    )


def render_scorecard_svg(artifacts: ScorecardArtifacts) -> str:
    status = artifacts.report["status"]
    rows = []
    for index, result in enumerate(artifacts.results):
        y = 40 + index * 20
        emoji = "✅" if result.ok else "❌"
        rows.append(
            f"<text x=\"10\" y=\"{y}\" font-size=\"12\">{emoji} {result.definition.label}: {result.formatted_observed()} (target {result.formatted_target()})</text>"
        )
    body = "".join(rows)
    header_color = "#4c9a2a" if status == "PASS" else "#cc3300"
    return (
        "<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"520\" height=\"" + str(40 + len(rows) * 20) + "\">"
        f"<rect width=\"520\" height=\"30\" fill=\"{header_color}\" rx=\"4\"/>"
        "<text x=\"10\" y=\"20\" font-size=\"16\" fill=\"#fff\">Sprint 6 Scorecards</text>"
        f"<text x=\"400\" y=\"20\" font-size=\"16\" fill=\"#fff\">{status}</text>"
        f"{body}</svg>"
    )


def ensure_output_dir() -> None:
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)


def write_text(path: Path, content: str) -> None:
    path.write_text(content, encoding="utf-8")


def write_json(path: Path, payload: Dict[str, Any]) -> None:
    path.write_text(json.dumps(payload, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


def write_guard_status(path: Path, status: str) -> None:
    path.write_text(f"{status}\n", encoding="utf-8")


def generate_report(
    *,
    threshold_path: Path = THRESHOLDS_PATH,
    metrics_path: Path = METRICS_PATH,
) -> ScorecardArtifacts:
    thresholds = load_json(threshold_path, "thresholds")
    metrics = load_json(metrics_path, "metrics")
    results = evaluate_metrics(thresholds, metrics)
    bundle_sha = compute_bundle_sha(thresholds, metrics)
    report = build_report(thresholds, metrics, results, bundle_sha)

    ensure_output_dir()
    artifacts = ScorecardArtifacts(
        report=report,
        results=results,
        bundle_sha256=bundle_sha,
        thresholds=thresholds,
        metrics=metrics,
    )
    write_json(OUTPUT_DIR / "report.json", report)
    write_text(OUTPUT_DIR / "report.md", render_markdown(artifacts))
    write_text(OUTPUT_DIR / "badge.svg", render_badge(report["status"]))
    write_text(OUTPUT_DIR / "scorecard.svg", render_scorecard_svg(artifacts))
    write_text(OUTPUT_DIR / "pr_comment.md", render_pr_comment(artifacts))
    write_text(OUTPUT_DIR / "bundle.sha256", bundle_sha + "\n")
    write_guard_status(OUTPUT_DIR / "guard_status.txt", report["status"])

    return artifacts


def main(argv: List[str] | None = None) -> int:
    _ = argv  # unused positional arguments; kept for compatibility
    artifacts = generate_report()
    print(f"S6 scorecards: {artifacts.report['status']} (bundle {artifacts.bundle_sha256})")
    return 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main(sys.argv[1:]))
