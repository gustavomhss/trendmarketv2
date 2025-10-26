#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import json
import sys
from dataclasses import dataclass
from datetime import datetime, timezone
from decimal import Decimal, ROUND_HALF_EVEN, getcontext
from pathlib import Path
from typing import Dict, List

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


@dataclass(frozen=True)
class MetricConfig:
    key: str
    threshold_key: str
    comparison: str
    display_name: str
    unit: str
    on_fail: str


@dataclass(frozen=True)
class Evaluation:
    config: MetricConfig
    observed: Decimal
    target: Decimal
    ok: bool


METRICS: List[MetricConfig] = [
    MetricConfig(
        key="quorum_ratio",
        threshold_key="quorum_ratio_min",
        comparison="gte",
        display_name="Quorum Ratio",
        unit="ratio",
        on_fail="Ativar fallback TWAP, reiniciar oráculos inativos e revisar alertas de quorum.",
    ),
    MetricConfig(
        key="failover_time_p95_s",
        threshold_key="failover_time_p95_s_max",
        comparison="lte",
        display_name="Failover p95",
        unit="seconds",
        on_fail="Executar runbook de failover e validar health-checks das rotas primárias.",
    ),
    MetricConfig(
        key="staleness_p95_s",
        threshold_key="staleness_p95_s_max",
        comparison="lte",
        display_name="Staleness p95",
        unit="seconds",
        on_fail="Investigar TWAP/heartbeats, checar latência de ingestão e recalibrar buffers.",
    ),
    MetricConfig(
        key="cdc_lag_p95_s",
        threshold_key="cdc_lag_p95_s_max",
        comparison="lte",
        display_name="CDC Lag p95",
        unit="seconds",
        on_fail="Acionar squad de dados para reequilibrar consumidores e ampliar throughput do stream.",
    ),
    MetricConfig(
        key="divergence_pct",
        threshold_key="divergence_pct_max",
        comparison="lte",
        display_name="Divergence %",
        unit="percent",
        on_fail="Rever pesos de feeds, habilitar overlays e comunicar incident commander.",
    ),
]

FORMATTERS = {
    "percent": lambda value: f"{value.quantize(Decimal('0.1'))}%",
    "ratio": lambda value: f"{value.quantize(Decimal('0.0001'))}",
    "seconds": lambda value: f"{value.quantize(Decimal('0.001'))}s",
}

SCHEMA_FILES = {
    "thresholds": SCHEMAS_DIR / "thresholds.schema.json",
    "metrics": SCHEMAS_DIR / "metrics.schema.json",
    "report": SCHEMAS_DIR / "report.schema.json",
}


def fail(code: str, message: str) -> None:
    raise RuntimeError(f"{ERROR_PREFIX}-E-{code}:{message}")


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


def decimal_from(value: object) -> Decimal:
    try:
        return Decimal(str(value))
    except Exception as exc:  # pragma: no cover
        fail("DECIMAL", f"Valor inválido para Decimal: {value} ({exc})")
        raise


def parse_thresholds(data: Dict) -> Dict[str, Decimal]:
    thresholds: Dict[str, Decimal] = {}
    for config in METRICS:
        if config.threshold_key not in data:
            fail("MISSING-THRESHOLD", f"Threshold ausente para {config.threshold_key}")
        thresholds[config.key] = decimal_from(data[config.threshold_key])
    return thresholds


def parse_measurements(data: Dict) -> Dict[str, Decimal]:
    measurements: Dict[str, Decimal] = {}
    for config in METRICS:
        if config.key not in data:
            fail("MISSING-METRIC", f"Métrica sem coleta: {config.key}")
        measurements[config.key] = decimal_from(data[config.key])
    return measurements


def compare(observed: Decimal, target: Decimal, comparison: str) -> bool:
    if comparison == "gte":
        return observed + EPSILON >= target
    if comparison == "lte":
        return observed - EPSILON <= target
    fail("COMPARISON", f"Operador desconhecido: {comparison}")
    return False


def evaluate(thresholds: Dict[str, Decimal], measurements: Dict[str, Decimal]) -> List[Evaluation]:
    evaluations: List[Evaluation] = []
    for config in METRICS:
        target = thresholds[config.key]
        observed = measurements.get(config.key)
        if observed is None:
            fail("MISSING-METRIC", f"Métrica sem coleta: {config.key}")
        ok = compare(observed, target, config.comparison)
        evaluations.append(Evaluation(config=config, observed=observed, target=target, ok=ok))
    return evaluations


def format_value(value: Decimal, unit: str) -> str:
    formatter = FORMATTERS.get(unit)
    if formatter is None:  # pragma: no cover
        return str(value)
    return formatter(value)


def canonical_dump(data: Dict) -> str:
    return json.dumps(data, sort_keys=True, ensure_ascii=False, separators=(",", ":")) + "\n"


def compute_bundle_sha(thresholds_raw: Dict, metrics_raw: Dict) -> str:
    payload = canonical_dump(thresholds_raw) + canonical_dump(metrics_raw)
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()


def build_report(
    evaluations: List[Evaluation],
    generated_at: str,
    thresholds_meta: Dict,
    metrics_meta: Dict,
    bundle_hash: str,
) -> Dict[str, object]:
    metrics_block: Dict[str, Dict[str, object]] = {}
    for evaluation in evaluations:
        config = evaluation.config
        metrics_block[config.key] = {
            "observed": float(evaluation.observed),
            "target": float(evaluation.target),
            "ok": evaluation.ok,
        }
    status = "PASS" if all(evaluation.ok for evaluation in evaluations) else "FAIL"
    return {
        "schema_version": 1,
        "timestamp_utc": generated_at,
        "status": status,
        "metrics": metrics_block,
        "inputs": {
            "thresholds": {
                "version": thresholds_meta["version"],
                "timestamp_utc": thresholds_meta["timestamp_utc"],
            },
            "metrics": {
                "version": metrics_meta["version"],
                "timestamp_utc": metrics_meta["timestamp_utc"],
            },
        },
        "bundle": {
            "sha256": bundle_hash,
        },
    }


def render_markdown(report: Dict[str, object], evaluations: List[Evaluation]) -> str:
    lines = ["# Sprint 6 Scorecards", ""]
    status_emoji = "✅" if report["status"] == "PASS" else "❌"
    lines.append(f"{status_emoji} Status geral: **{report['status']}**")
    lines.append("")
    lines.append("| Métrica | Observado | Limite | Status |")
    lines.append("| --- | --- | --- | --- |")
    for evaluation in evaluations:
        config = evaluation.config
        status = "✅" if evaluation.ok else "❌"
        lines.append(
            "| {name} | {observed} | {target} | {status} |".format(
                name=config.display_name,
                observed=format_value(evaluation.observed, config.unit),
                target=format_value(evaluation.target, config.unit),
                status=status,
            )
        )
    lines.append("")
    lines.append("## O que fazer agora")
    failing = [evaluation for evaluation in evaluations if not evaluation.ok]
    if failing:
        for evaluation in failing:
            lines.append(f"- {evaluation.config.display_name}: {evaluation.config.on_fail}")
    else:
        lines.append("- Todas as métricas atendidas. Continuar monitoramento e revisar novamente em 24h.")
    lines.append("")
    lines.append("## Metadados")
    lines.append(
        f"- Thresholds: v{report['inputs']['thresholds']['version']} @ {report['inputs']['thresholds']['timestamp_utc']}"
    )
    lines.append(
        f"- Métricas: v{report['inputs']['metrics']['version']} @ {report['inputs']['metrics']['timestamp_utc']}"
    )
    lines.append(f"- Gerado em: {report['timestamp_utc']}")
    lines.append(f"- SHA do bundle: `{report['bundle']['sha256']}`")
    return "\n".join(lines) + "\n"


def build_pr_comment(report: Dict[str, object], evaluations: List[Evaluation]) -> str:
    emoji = "✅" if report["status"] == "PASS" else "❌"
    lines = [f"{emoji} [Sprint 6 report](./report.md)"]
    lines.append("")
    lines.append("![Status](./badge.svg)")
    lines.append("")
    lines.append("## O que fazer agora")
    failing = [evaluation for evaluation in evaluations if not evaluation.ok]
    if failing:
        for evaluation in failing:
            lines.append(f"- {evaluation.config.display_name}: {evaluation.config.on_fail}")
    else:
        lines.append("- Nenhuma ação imediata necessária.")
    lines.append("")
    lines.append("Detalhes completos em [report.md](./report.md).")
    return "\n".join(lines) + "\n"


def render_svg_badge(report: Dict[str, object]) -> str:
    status = report["status"]
    label_color = "#2e8540" if status == "PASS" else "#c92a2a"
    return (
        "<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"160\" height=\"40\">"
        f"<rect width=\"160\" height=\"40\" fill=\"{label_color}\" rx=\"6\"/>"
        "<text x=\"80\" y=\"25\" text-anchor=\"middle\" fill=\"#ffffff\" font-size=\"20\""
        f" font-family=\"Helvetica,Arial,sans-serif\">S6 {status}</text>"
        "</svg>"
    )


def render_scorecard_svg(evaluations: List[Evaluation]) -> str:
    rows = len(evaluations)
    height = 60 + 30 * rows
    header = (
        f"<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"520\" height=\"{height}\">"
        "<style>text{font-family:Helvetica,Arial,sans-serif;font-size:14px;}</style>"
        f"<rect width=\"520\" height=\"{height}\" fill=\"#ffffff\" stroke=\"#1f2933\" rx=\"8\"/>"
        "<text x=\"20\" y=\"30\" font-size=\"18\" font-weight=\"bold\">Sprint 6 Scorecards</text>"
    )
    lines = [header]
    y = 60
    for evaluation in evaluations:
        config = evaluation.config
        status_color = "#2e8540" if evaluation.ok else "#c92a2a"
        status_text = "PASS" if evaluation.ok else "FAIL"
        lines.append(
            f"<text x=\"20\" y=\"{y}\">{config.display_name}</text>"
            f"<text x=\"260\" y=\"{y}\">{format_value(evaluation.observed, config.unit)}</text>"
            f"<text x=\"360\" y=\"{y}\">{format_value(evaluation.target, config.unit)}</text>"
            f"<text x=\"460\" y=\"{y}\" fill=\"{status_color}\">{status_text}</text>"
        )
        y += 30
    lines.append("</svg>")
    return "".join(lines)


def write_file(path: Path, content: str) -> None:
    path.write_text(content, encoding="utf-8")


def write_outputs(report: Dict[str, object], evaluations: List[Evaluation]) -> None:
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)
    write_file(OUTPUT_DIR / "report.json", json.dumps(report, indent=2, ensure_ascii=False) + "\n")
    markdown = render_markdown(report, evaluations)
    write_file(OUTPUT_DIR / "report.md", markdown)
    write_file(OUTPUT_DIR / "pr_comment.md", build_pr_comment(report, evaluations))
    badge_svg = render_svg_badge(report)
    write_file(OUTPUT_DIR / "badge.svg", badge_svg + "\n")
    scorecard_svg = render_scorecard_svg(evaluations)
    write_file(OUTPUT_DIR / "scorecard.svg", scorecard_svg + "\n")
    write_file(OUTPUT_DIR / "guard_status.txt", report["status"] + "\n")
    write_file(OUTPUT_DIR / "bundle.sha256", report["bundle"]["sha256"] + "\n")


def generate_report(threshold_path: Path = THRESHOLD_PATH, metrics_path: Path = METRICS_PATH) -> Dict[str, object]:
    try:
        thresholds_raw = load_json(threshold_path, "thresholds")
        metrics_raw = load_json(metrics_path, "metrics")
        thresholds = parse_thresholds(thresholds_raw)
        measurements = parse_measurements(metrics_raw)
        evaluations = evaluate(thresholds, measurements)
        generated_at = datetime.now(timezone.utc).replace(microsecond=0).isoformat()
        bundle_hash = compute_bundle_sha(thresholds_raw, metrics_raw)
        report = build_report(evaluations, generated_at, thresholds_raw, metrics_raw, bundle_hash)
        write_outputs(report, evaluations)
    except RuntimeError as exc:
        print(f"FAIL {exc}")
        OUTPUT_DIR.mkdir(parents=True, exist_ok=True)
        write_file(OUTPUT_DIR / "guard_status.txt", "FAIL\n")
        raise
    else:
        print("PASS Sprint 6 scorecards")
        return report


def main() -> int:
    try:
        generate_report()
    except RuntimeError:
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
