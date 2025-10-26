#!/usr/bin/env python3
"""Sprint 6 scorecard generator."""

from __future__ import annotations

import hashlib
import json
import sys
from dataclasses import dataclass
from datetime import datetime, timezone
from decimal import Decimal, ROUND_HALF_EVEN, getcontext
from functools import lru_cache
from pathlib import Path
from typing import Any, Dict, Iterable, List

BASE_DIR = Path(__file__).resolve().parents[2]
sys.path.append(str(BASE_DIR))

from jsonschema import Draft7Validator, ValidationError
import jsonschema  

getcontext().prec = 28
getcontext().rounding = ROUND_HALF_EVEN


EPSILON = Decimal("1e-12")
ERROR_PREFIX = "S6"
SCHEMA_VERSION = 1


SCHEMA_FILES = {
    "thresholds": SCHEMAS_DIR / "thresholds.schema.json",
    "metrics": SCHEMAS_DIR / "metrics.schema.json",
    "report": SCHEMAS_DIR / "report.schema.json",
}


@dataclass(frozen=True)
class MetricDefinition:
    key: str
    label: str
    comparator: str
    unit: str
    quantize: Decimal
    runbook: str


@dataclass(frozen=True)
class MetricResult:
    definition: MetricDefinition
    observed: Decimal
    target: Decimal
    ok: bool

    def observed_quantized(self) -> Decimal:
        return self.observed.quantize(self.definition.quantize)

    def target_quantized(self) -> Decimal:
        return self.target.quantize(self.definition.quantize)

    def observed_for_json(self) -> float:
        return float(self.observed_quantized())

    def target_for_json(self) -> float:
        return float(self.target_quantized())

    def formatted_observed(self) -> str:
        return format_value(self.observed_quantized(), self.definition.unit)

    def formatted_target(self) -> str:
        return format_value(self.target_quantized(), self.definition.unit)

    def status_text(self) -> str:
        return "PASS" if self.ok else "FAIL"


@dataclass(frozen=True)
class ScorecardArtifacts:
    report: Dict[str, object]
    results: List[MetricResult]
    bundle_sha256: str
    thresholds_version: int
    metrics_version: int


class ScorecardError(RuntimeError):
    """Error raised for deterministic scorecard failures."""

    def __init__(self, code: str, message: str) -> None:
        super().__init__(f"{code}:{message}")
        self.code = code
        self.message = message


METRIC_DEFINITIONS: List[MetricDefinition] = [
    MetricDefinition(
        key="quorum_ratio",
        label="Quorum Ratio",
        comparator="gte",
        unit="ratio",
        quantize=Decimal("0.0001"),
        runbook="Ativar fallback TWAP, reiniciar oráculos inativos e revisar alertas de quorum.",
    ),
    MetricDefinition(
        key="failover_time_p95_s",
        label="Failover Time p95 (s)",
        comparator="lte",
        unit="seconds",
        quantize=Decimal("0.001"),
        runbook="Executar runbook de failover e validar health-checks das rotas primárias.",
    ),
    MetricDefinition(
        key="staleness_p95_s",
        label="Staleness p95 (s)",
        comparator="lte",
        unit="seconds",
        quantize=Decimal("0.001"),
        runbook="Investigar TWAP/heartbeats, checar latência de ingestão e recalibrar buffers.",
    ),
    MetricDefinition(
        key="cdc_lag_p95_s",
        label="CDC Lag p95 (s)",
        comparator="lte",
        unit="seconds",
        quantize=Decimal("0.001"),
        runbook="Acionar squad de dados para reequilibrar consumidores e ampliar throughput do stream.",
    ),
    MetricDefinition(
        key="divergence_pct",
        label="Divergence (%)",
        comparator="lte",
        unit="percent",
        quantize=Decimal("0.1"),
        runbook="Rever pesos de feeds, habilitar overlays e comunicar incident commander.",
    ),
]


def fail(code_suffix: str, message: str) -> None:
    raise ScorecardError(f"{ERROR_PREFIX}-E-{code_suffix}", message)

_FORMAT_CHECKER = jsonschema.FormatChecker()
_SCHEMA_VALIDATORS: dict[str, jsonschema.Draft7Validator] = {}


def _validator_for(schema_key: str) -> jsonschema.Draft7Validator:
    try:
        return _SCHEMA_VALIDATORS[schema_key]
    except KeyError:
        schema_path = SCHEMA_FILES[schema_key]
        schema = json.loads(schema_path.read_text(encoding="utf-8"))
        validator = jsonschema.Draft7Validator(schema, format_checker=_FORMAT_CHECKER)
        _SCHEMA_VALIDATORS[schema_key] = validator
        return validator


@lru_cache(maxsize=None)
def _load_schema(schema_key: str) -> Dict[str, Any]:
    schema_path = SCHEMA_FILES[schema_key]
    with schema_path.open("r", encoding="utf-8") as handle:
        return json.load(handle)


@lru_cache(maxsize=None)
def _get_validator(schema_key: str) -> Draft7Validator:
    schema = _load_schema(schema_key)
    return Draft7Validator(schema)


def load_json(path: Path, schema_key: str) -> Dict:
def load_json(path: Path, schema_key: str) -> Dict[str, object]:
    if not path.exists():
        fail("MISSING", f"Arquivo obrigatório ausente: {path}")
    try:
        raw_text = path.read_text(encoding="utf-8")
    except UnicodeDecodeError as exc:  # pragma: no cover - defensive
        fail("ENCODING", f"Arquivo não está em UTF-8: {path}: {exc}")
    except OSError as exc:  # pragma: no cover - defensive
        fail("IO", f"Falha ao ler {path}: {exc}")
    try:
        content = json.loads(raw_text)
    except json.JSONDecodeError as exc:
        fail("INVALID-JSON", f"Falha ao decodificar {path}: {exc}")
    try:
        validator = _validator_for(schema_key)
        validator.validate(content)
    except jsonschema.ValidationError as exc:
        location = "/".join(str(part) for part in exc.path)
        suffix = f" (campo {location})" if location else ""
        fail("SCHEMA", f"Violação de schema em {path}: {exc.message}{suffix}")

    schema_path = SCHEMA_FILES[schema_key]
    schema = json.loads(schema_path.read_text(encoding="utf-8"))
    try:
        validator = _get_validator(schema_key)
        validator.validate(content)
    except ValidationError as exc:
        fail("SCHEMA", f"Violação de schema em {path}: {exc.message}")
    return content


def decimal_from(value: object) -> Decimal:
    if isinstance(value, Decimal):
        return value
    if isinstance(value, (int, float, str)):
        try:
            return Decimal(str(value))
        except Exception as exc:  # pragma: no cover - Decimal conversion errors
            fail("DECIMAL", f"Valor inválido {value!r}: {exc}")
    fail("DECIMAL", f"Valor não numérico: {value!r}")


def compare(observed: Decimal, target: Decimal, comparator: str) -> bool:
    if comparator == "gte":
        return observed + EPSILON >= target
    if comparator == "lte":
        return observed - EPSILON <= target
    fail("COMPARATOR", f"Operador inválido: {comparator}")
    return False


def evaluate_metrics(thresholds: Dict[str, object], metrics: Dict[str, object]) -> List[MetricResult]:
    results: List[MetricResult] = []
    for definition in METRIC_DEFINITIONS:
        if definition.key not in thresholds:
            fail("MISSING-THRESHOLD", f"Threshold ausente para {definition.key}")
        if definition.key not in metrics:
            fail("MISSING-METRIC", f"Métrica ausente: {definition.key}")
        target = decimal_from(thresholds[definition.key])
        observed = decimal_from(metrics[definition.key])
        ok = compare(observed, target, definition.comparator)
        results.append(MetricResult(definition=definition, observed=observed, target=target, ok=ok))
    return results


def compute_status(results: Iterable[MetricResult]) -> str:
    return "PASS" if all(result.ok for result in results) else "FAIL"


def isoformat_utc() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def canonical_json(data: Dict[str, object]) -> str:
    return json.dumps(data, sort_keys=True, ensure_ascii=False, separators=(",", ":")) + "\n"


def build_report(
    results: List[MetricResult],
    generated_at: str,
    thresholds_meta: Dict[str, object],
    metrics_meta: Dict[str, object],
    bundle_hash: str,
) -> Dict[str, object]:
    metrics_block = {
        result.definition.key: {
            "observed": result.observed_for_json(),
            "target": result.target_for_json(),
            "ok": result.ok,
        }
        for result in results
    }
    return {
        "schema_version": SCHEMA_VERSION,
        "timestamp_utc": generated_at,
        "status": compute_status(results),
        "metrics": metrics_block,
        "inputs": {
            "thresholds": {
                "version": int(thresholds_meta["version"]),
                "timestamp_utc": thresholds_meta["timestamp_utc"],
            },
            "metrics": {
                "version": int(metrics_meta["version"]),
                "timestamp_utc": metrics_meta["timestamp_utc"],
            },
        },
        "bundle": {"sha256": bundle_hash},
    }


def render_markdown(
    report: Dict[str, object],
    results: List[MetricResult],
    bundle_sha256: str,
) -> str:
    emoji = "✅" if report["status"] == "PASS" else "❌"
    lines = ["# Sprint 6 Scorecards", ""]
    lines.append(f"{emoji} Status geral: **{report['status']}**")
    lines.append("")
    lines.append(f"- Timestamp UTC: {report['timestamp_utc']}")
    lines.append(
        "- Thresholds: v{version} @ {ts}".format(
            version=report["inputs"]["thresholds"]["version"],
            ts=report["inputs"]["thresholds"]["timestamp_utc"],
        )
    )
    lines.append(
        "- Métricas: v{version} @ {ts}".format(
            version=report["inputs"]["metrics"]["version"],
            ts=report["inputs"]["metrics"]["timestamp_utc"],
        )
    )
    lines.append(f"- SHA do bundle: `{bundle_sha256}`")
    lines.append("")
    lines.append("| Métrica | Observado | Alvo | Status |")
    lines.append("| --- | --- | --- | --- |")
    for result in results:
        emoji_metric = "✅" if result.ok else "❌"
        lines.append(
            "| {label} | {observed} | {target} | {status} {text} |".format(
                label=result.definition.label,
                observed=result.formatted_observed(),
                target=result.formatted_target(),
                status=emoji_metric,
                text=result.status_text(),
            )
        )
    lines.append("")
    lines.append("## O que fazer agora")
    failing = [result for result in results if not result.ok]
    if failing:
        for result in failing:
            lines.append(f"- {result.definition.label}: {result.definition.runbook}")
    else:
        lines.append("- Todas as métricas passaram. Manter monitoramento em 24h.")
    lines.append("")
    return "\n".join(lines) + "\n"


def build_pr_comment(report: Dict[str, object], bundle_sha256: str, results: List[MetricResult]) -> str:
    emoji = "✅" if report["status"] == "PASS" else "❌"
    lines = [f"{emoji} [Sprint 6 report](./report.md)", ""]
    lines.append("![Status](./badge.svg)")
    lines.append("")
    lines.append("## Métricas")
    for result in results:
        lines.append(
            "- {label}: {observed} (alvo {target}) — {status}".format(
                label=result.definition.label,
                observed=result.formatted_observed(),
                target=result.formatted_target(),
                status=result.status_text(),
            )
        )
    lines.append("")
    lines.append("## Metadados")
    lines.append(
        "- Thresholds: v{version} @ {ts}".format(
            version=report["inputs"]["thresholds"]["version"],
            ts=report["inputs"]["thresholds"]["timestamp_utc"],
        )
    )
    lines.append(
        "- Métricas: v{version} @ {ts}".format(
            version=report["inputs"]["metrics"]["version"],
            ts=report["inputs"]["metrics"]["timestamp_utc"],
        )
    )
    lines.append(f"- Gerado em: {report['timestamp_utc']}")
    lines.append(f"- Bundle SHA-256: `{bundle_sha256}`")
    lines.append("")
    lines.append("Relatório completo disponível em [report.md](./report.md).")
    return "\n".join(lines) + "\n"


def render_svg_badge(status: str) -> str:
    color = "#2e8540" if status == "PASS" else "#c92a2a"
    return (
        "<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"160\" height=\"40\" role=\"img\">"
        f"<title>S6 {status}</title>"
        f"<rect width=\"160\" height=\"40\" rx=\"6\" fill=\"{color}\"/>"
        "<text x=\"80\" y=\"25\" text-anchor=\"middle\" fill=\"#ffffff\""
        " font-family=\"Helvetica,Arial,sans-serif\" font-size=\"18\">S6 "
        f"{status}</text></svg>"
    )


def render_scorecard_svg(status: str, results: List[MetricResult]) -> str:
    rows = len(results)
    height = 60 + 30 * rows
    header = (
        f"<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"520\" height=\"{height}\">"
        "<style>text{font-family:Helvetica,Arial,sans-serif;font-size:14px;}</style>"
        f"<rect width=\"520\" height=\"{height}\" rx=\"8\" fill=\"#ffffff\" stroke=\"#1f2933\"/>"
        "<text x=\"20\" y=\"30\" font-size=\"18\" font-weight=\"bold\">Sprint 6 Scorecards</text>"
        f"<text x=\"500\" y=\"30\" text-anchor=\"end\" font-size=\"16\">Status: {status}</text>"
        "<text x=\"20\" y=\"52\" font-weight=\"bold\">Métrica</text>"
        "<text x=\"260\" y=\"52\" font-weight=\"bold\">Observado</text>"
        "<text x=\"380\" y=\"52\" font-weight=\"bold\">Alvo</text>"
        "<text x=\"470\" y=\"52\" font-weight=\"bold\">Status</text>"
    )
    lines = [header]
    y = 82
    for result in results:
        color = "#2e8540" if result.ok else "#c92a2a"
        lines.append(
            f"<text x=\"20\" y=\"{y}\">{result.definition.label}</text>"
            f"<text x=\"260\" y=\"{y}\">{result.formatted_observed()}</text>"
            f"<text x=\"380\" y=\"{y}\">{result.formatted_target()}</text>"
            f"<text x=\"470\" y=\"{y}\" fill=\"{color}\">{result.status_text()}</text>"
        )
        y += 30
    lines.append("</svg>")
    return "".join(lines)


def ensure_output_dir() -> None:
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)


def write_outputs(
    report: Dict[str, object],
    results: List[MetricResult],
    bundle_sha256: str,
) -> None:
    ensure_output_dir()
    (OUTPUT_DIR / "report.json").write_text(
        json.dumps(report, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    markdown = render_markdown(report, results, bundle_sha256)
    (OUTPUT_DIR / "report.md").write_text(markdown, encoding="utf-8")
    pr_comment = build_pr_comment(report, bundle_sha256, results)
    (OUTPUT_DIR / "pr_comment.md").write_text(pr_comment, encoding="utf-8")
    badge_svg = render_svg_badge(report["status"])
    (OUTPUT_DIR / "badge.svg").write_text(badge_svg + "\n", encoding="utf-8")
    scorecard_svg = render_scorecard_svg(report["status"], results)
    (OUTPUT_DIR / "scorecard.svg").write_text(scorecard_svg + "\n", encoding="utf-8")
    (OUTPUT_DIR / "guard_status.txt").write_text(report["status"] + "\n", encoding="utf-8")
    (OUTPUT_DIR / "bundle.sha256").write_text(bundle_sha256 + "\n", encoding="utf-8")


def generate_report(
    threshold_path: Path = THRESHOLD_PATH,
    metrics_path: Path = METRICS_PATH,
) -> ScorecardArtifacts:
    thresholds_raw = load_json(threshold_path, "thresholds")
    metrics_raw = load_json(metrics_path, "metrics")
    results = evaluate_metrics(thresholds_raw, metrics_raw)
    generated_at = isoformat_utc()
    bundle_payload = canonical_json(thresholds_raw) + canonical_json(metrics_raw)
    bundle_hash = hashlib.sha256(bundle_payload.encode("utf-8")).hexdigest()
    report = build_report(results, generated_at, thresholds_raw, metrics_raw, bundle_hash)
    write_outputs(report, results, bundle_hash)
    return ScorecardArtifacts(
        report=report,
        results=results,
        bundle_sha256=bundle_hash,
        thresholds_version=int(thresholds_raw["version"]),
        metrics_version=int(metrics_raw["version"]),
    )


def format_value(value: Decimal, unit: str) -> str:
    if unit == "percent":
        return f"{value.quantize(Decimal('0.1'))}%"
    if unit == "ratio":
        return f"{value.quantize(Decimal('0.0001'))}"
    if unit == "seconds":
        return f"{value.quantize(Decimal('0.001'))}s"
    return format(value, "f")


def main() -> int:
    try:
        artifacts = generate_report()
    except ScorecardError as exc:
        ensure_output_dir()
        (OUTPUT_DIR / "guard_status.txt").write_text("FAIL\n", encoding="utf-8")
        print(f"FAIL {exc}")
        return 1
    else:
        print(f"{artifacts.report['status']} Sprint 6 scorecards")
        return 0


if __name__ == "__main__":
    raise SystemExit(main())
