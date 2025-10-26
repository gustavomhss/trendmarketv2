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

SCHEMA_VERSION = 1
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


METRIC_TARGET_KEYS: Dict[str, str] = {
    "quorum_ratio": "quorum_ratio_min",
    "failover_time_p95_s": "failover_time_p95_s_max",
    "staleness_p95_s": "staleness_p95_s_max",
    "cdc_lag_p95_s": "cdc_lag_p95_s_max",
    "divergence_pct": "divergence_pct_max",
}


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
        target_key = METRIC_TARGET_KEYS[definition.key]
        if target_key not in thresholds:
            fail("MISSING-THRESHOLD", f"Threshold ausente para {definition.key}")
        if definition.key not in metrics:
            fail("MISSING-METRIC", f"Métrica ausente: {definition.key}")
        target = decimal_from(thresholds[target_key])
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
        "schema": "trendmarketv2.sprint6.report",
        "schema_version": SCHEMA_VERSION,
        "timestamp_utc": isoformat_utc(),
        "status": status,
        "metrics": metrics_block,
        "inputs": {
            "thresholds": {
                "schema": thresholds.get("schema"),
                "version": thresholds.get("version"),
                "timestamp_utc": thresholds.get("timestamp_utc"),
            },
            "metrics": {
                "schema": metrics.get("schema"),
                "version": metrics.get("version"),
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
    lines.append(f"- Relatório gerado em: {report['timestamp_utc']}")
    lines.append(
        f"- Thresholds: v{report['inputs']['thresholds']['version']} @ {report['inputs']['thresholds']['timestamp_utc']}"
    )
    lines.append(f"- Métricas: v{report['inputs']['metrics']['version']} @ {report['inputs']['metrics']['timestamp_utc']}")
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
