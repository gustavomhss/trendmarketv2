#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass
from datetime import datetime, timezone
from decimal import Decimal, ROUND_HALF_EVEN, getcontext
from functools import lru_cache
from pathlib import Path
from typing import Any, Dict, Iterable, List

from jsonschema import Draft7Validator, ValidationError

BASE_DIR = Path(__file__).resolve().parents[2]

getcontext().prec = 28
getcontext().rounding = ROUND_HALF_EVEN

EPSILON = Decimal("1e-12")
THRESHOLD_PATH = BASE_DIR / "s6_validation" / "thresholds.json"
METRICS_PATH = BASE_DIR / "s6_validation" / "metrics_static.json"
SCHEMAS_DIR = BASE_DIR / "schemas"
OUTPUT_DIR = BASE_DIR / "out" / "s6_scorecards"
ERROR_PREFIX = "S6"
SCHEMA_VERSION = 1


class ScorecardError(RuntimeError):
    """Exception raised for scorecard failures with a canonical code."""

    def __init__(self, code: str, message: str) -> None:
        self.code = f"{ERROR_PREFIX}-E-{code}"
        self.message = message
        super().__init__(f"{self.code}:{message}")


def fail(code: str, message: str) -> None:
    raise ScorecardError(code, message)


@dataclass(frozen=True)
class MetricSpec:
    key: str
    label: str
    threshold_key: str
    comparison: str
    quantize: Decimal
    markdown_suffix: str
    unit: str
    on_fail: str


@dataclass(frozen=True)
class MetricResult:
    spec: MetricSpec
    observed: Decimal
    target: Decimal
    ok: bool

    def observed_quantized(self) -> Decimal:
        return self.observed.quantize(self.spec.quantize)

    def target_quantized(self) -> Decimal:
        return self.target.quantize(self.spec.quantize)

    def observed_for_json(self) -> float:
        return float(self.observed_quantized())

    def target_for_json(self) -> float:
        return float(self.target_quantized())

    def formatted_observed(self) -> str:
        return _format_decimal(self.observed_quantized(), self.spec.markdown_suffix)

    def formatted_target(self) -> str:
        return _format_decimal(self.target_quantized(), self.spec.markdown_suffix)

    def status_text(self) -> str:
        return "PASS" if self.ok else "FAIL"


@dataclass(frozen=True)
class ScorecardArtifacts:
    report: Dict[str, object]
    results: List[MetricResult]
    bundle_sha256: str
    thresholds_version: int
    metrics_version: int


METRIC_SPECS: List[MetricSpec] = [
    MetricSpec(
        key="quorum_ratio",
        label="Quorum Ratio",
        threshold_key="quorum_ratio_min",
        comparison="gte",
        quantize=Decimal("0.0001"),
        markdown_suffix="",
        unit="ratio",
        on_fail="Ativar fallback TWAP, reiniciar oráculos inativos e revisar alertas de quorum.",
    ),
    MetricSpec(
        key="failover_time_p95_s",
        label="Failover Time p95 (s)",
        threshold_key="failover_time_p95_s_max",
        comparison="lte",
        quantize=Decimal("0.001"),
        markdown_suffix="s",
        unit="seconds",
        on_fail="Executar runbook de failover e validar health-checks das rotas primárias.",
    ),
    MetricSpec(
        key="staleness_p95_s",
        label="Staleness p95 (s)",
        threshold_key="staleness_p95_s_max",
        comparison="lte",
        quantize=Decimal("0.001"),
        markdown_suffix="s",
        unit="seconds",
        on_fail="Investigar TWAP/heartbeats, checar latência de ingestão e recalibrar buffers.",
    ),
    MetricSpec(
        key="cdc_lag_p95_s",
        label="CDC Lag p95 (s)",
        threshold_key="cdc_lag_p95_s_max",
        comparison="lte",
        quantize=Decimal("0.001"),
        markdown_suffix="s",
        unit="seconds",
        on_fail="Acionar squad de dados para reequilibrar consumidores e ampliar throughput do stream.",
    ),
    MetricSpec(
        key="divergence_pct",
        label="Divergence (%)",
        threshold_key="divergence_pct_max",
        comparison="lte",
        quantize=Decimal("0.1"),
        markdown_suffix="%",
        unit="percent",
        on_fail="Rever pesos de feeds, habilitar overlays e comunicar incident commander.",
    ),
]


SCHEMA_FILES = {
    "thresholds": SCHEMAS_DIR / "thresholds.schema.json",
    "metrics": SCHEMAS_DIR / "metrics.schema.json",
    "report": SCHEMAS_DIR / "report.schema.json",
}


def _format_decimal(value: Decimal, suffix: str) -> str:
    text = format(value, "f")
    return text + suffix if suffix else text


@lru_cache(maxsize=None)
def _load_schema(schema_key: str) -> Dict[str, Any]:
    schema_path = SCHEMA_FILES[schema_key]
    try:
        return json.loads(schema_path.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:  # pragma: no cover - configuration error
        fail("SCHEMA-MISSING", f"Schema ausente: {schema_path}: {exc}")
    except json.JSONDecodeError as exc:  # pragma: no cover - configuration error
        fail("SCHEMA-INVALID", f"Schema inválido em {schema_path}: {exc}")


@lru_cache(maxsize=None)
def _get_validator(schema_key: str) -> Draft7Validator:
    schema = _load_schema(schema_key)
    return Draft7Validator(schema)


def load_json(path: Path, schema_key: str) -> Dict[str, Any]:
    if not path.exists():
        fail("MISSING", f"Arquivo obrigatório ausente: {path}")
    try:
        raw_text = path.read_text(encoding="utf-8")
    except UnicodeDecodeError as exc:
        fail("ENCODING", f"Arquivo não está em UTF-8: {path}: {exc}")
    except OSError as exc:
        fail("IO", f"Falha ao ler {path}: {exc}")
    try:
        content = json.loads(raw_text)
    except json.JSONDecodeError as exc:
        fail("INVALID-JSON", f"Falha ao decodificar {path}: {exc}")
    validator = _get_validator(schema_key)
    try:
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
        except Exception as exc:  # pragma: no cover - defensive
            fail("DECIMAL", f"Valor inválido para Decimal: {value} ({exc})")
    fail("DECIMAL", f"Valor não numérico: {value}")


def evaluate_metrics(thresholds: Dict[str, Any], metrics: Dict[str, Any]) -> List[MetricResult]:
    results: List[MetricResult] = []
    for spec in METRIC_SPECS:
        if spec.threshold_key not in thresholds:
            fail("MISSING-THRESHOLD", f"Threshold ausente para {spec.threshold_key}")
        if spec.key not in metrics:
            fail("MISSING-METRIC", f"Métrica sem coleta: {spec.key}")
        observed = decimal_from(metrics[spec.key])
        target = decimal_from(thresholds[spec.threshold_key])
        if spec.comparison == "gte":
            ok = observed + EPSILON >= target
        elif spec.comparison == "lte":
            ok = observed - EPSILON <= target
        else:  # pragma: no cover - configuration error
            fail("COMPARISON", f"Operador desconhecido: {spec.comparison}")
        results.append(MetricResult(spec=spec, observed=observed, target=target, ok=bool(ok)))
    return results


def compute_status(results: Iterable[MetricResult]) -> str:
    return "PASS" if all(result.ok for result in results) else "FAIL"


def isoformat_utc() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def canonical_dumps(data: Dict[str, Any]) -> str:
    return json.dumps(data, sort_keys=True, ensure_ascii=False, separators=(",", ":")) + "
"


def ensure_output_dir() -> None:
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)


def render_markdown(
    report: Dict[str, Any],
    results: List[MetricResult],
    bundle_sha256: str,
    thresholds_version: int,
    metrics_version: int,
) -> str:
    lines = ["# Sprint 6 Scorecards", ""]
    status = report["status"]
    lines.append(f"{'✅' if status == 'PASS' else '❌'} Status geral: **{status}**")
    lines.append("")
    lines.append(f"- Timestamp UTC: {report['timestamp_utc']}")
    lines.append(f"- Versão dos thresholds: {thresholds_version}")
    lines.append(f"- Versão das métricas: {metrics_version}")
    lines.append(f"- SHA do bundle: `{bundle_sha256}`")
    lines.append("")
    lines.append("| Métrica | Observado | Alvo | Status |")
    lines.append("| --- | --- | --- | --- |")
    for result in results:
        emoji = "✅" if result.ok else "❌"
        lines.append(
            f"| {result.spec.label} | {result.formatted_observed()} | {result.formatted_target()} | {emoji} {result.status_text()} |"
        )
    lines.append("")
    lines.append("## O que fazer agora")
    failing = [result for result in results if not result.ok]
    if failing:
        for result in failing:
            lines.append(f"- {result.spec.label}: {result.spec.on_fail}")
    else:
        lines.append("- Todas as métricas passaram. Manter monitoramento em 24h.")
    lines.append("")
    return "
".join(lines) + "
"


def build_pr_comment(report: Dict[str, Any], results: List[MetricResult], bundle_sha256: str) -> str:
    emoji = "✅" if report["status"] == "PASS" else "❌"
    lines = [f"{emoji} [Sprint 6 report](./report.md)"]
    lines.append("")
    lines.append("![Status](./badge.svg)")
    lines.append("")
    lines.append("## O que fazer agora")
    failing = [result for result in results if not result.ok]
    if failing:
        for result in failing:
            lines.append(f"- {result.spec.label}: {result.spec.on_fail}")
    else:
        lines.append("- Nenhuma ação imediata necessária.")
    lines.append("")
    lines.append(f"Bundle SHA-256: `{bundle_sha256}`")
    lines.append("")
    lines.append("Relatório completo disponível em [report.md](./report.md).")
    return "
".join(lines) + "
"


def render_svg_badge(status: str) -> str:
    color = "#2e8540" if status == "PASS" else "#c92a2a"
    return (
        "<svg xmlns="http://www.w3.org/2000/svg" width="160" height="40">"
        f"<rect width="160" height="40" fill="{color}" rx="6"/>"
        f"<text x="80" y="25" text-anchor="middle" fill="#ffffff" font-size="20""
        " font-family="Helvetica,Arial,sans-serif">S6 {status}</text>"
        "</svg>"
    )


def render_scorecard_svg(status: str, results: List[MetricResult]) -> str:
    rows = len(results)
    height = 80 + rows * 30
    svg = [
        f"<svg xmlns="http://www.w3.org/2000/svg" width="520" height="{height}">",
        "<style>text{font-family:Helvetica,Arial,sans-serif;font-size:14px;}</style>",
        f"<rect width="520" height="{height}" fill="#ffffff" stroke="#1f2933" rx="8"/>",
        "<text x="20" y="30" font-size="18" font-weight="bold">Sprint 6 Scorecards</text>",
        f"<text x="420" y="30" text-anchor="end" font-size="16">Status: {status}</text>",
        "<text x="20" y="60" font-weight="bold">Métrica</text>",
        "<text x="260" y="60" font-weight="bold">Observado</text>",
        "<text x="370" y="60" font-weight="bold">Alvo</text>",
        "<text x="470" y="60" font-weight="bold">Status</text>",
    ]
    y = 90
    for result in results:
        status_color = "#2e8540" if result.ok else "#c92a2a"
        svg.append(f"<text x="20" y="{y}">{result.spec.label}</text>")
        svg.append(f"<text x="260" y="{y}">{result.formatted_observed()}</text>")
        svg.append(f"<text x="370" y="{y}">{result.formatted_target()}</text>")
        svg.append(
            f"<text x="470" y="{y}" fill="{status_color}" text-anchor="end">{result.status_text()}</text>"
        )
        y += 30
    svg.append("</svg>")
    return "".join(svg)


def write_outputs(
    report: Dict[str, Any],
    results: List[MetricResult],
    bundle_sha256: str,
    thresholds_version: int,
    metrics_version: int,
) -> None:
    ensure_output_dir()
    (OUTPUT_DIR / "report.json").write_text(
        json.dumps(report, indent=2, ensure_ascii=False) + "
",
        encoding="utf-8",
    )
    markdown = render_markdown(report, results, bundle_sha256, thresholds_version, metrics_version)
    (OUTPUT_DIR / "report.md").write_text(markdown, encoding="utf-8")
    pr_comment = build_pr_comment(report, results, bundle_sha256)
    (OUTPUT_DIR / "pr_comment.md").write_text(pr_comment, encoding="utf-8")
    badge_svg = render_svg_badge(report["status"])
    (OUTPUT_DIR / "badge.svg").write_text(badge_svg + "
", encoding="utf-8")
    scorecard_svg = render_scorecard_svg(report["status"], results)
    (OUTPUT_DIR / "scorecard.svg").write_text(scorecard_svg + "
", encoding="utf-8")
    (OUTPUT_DIR / "guard_status.txt").write_text(report["status"] + "
", encoding="utf-8")
    (OUTPUT_DIR / "bundle.sha256").write_text(bundle_sha256 + "
", encoding="utf-8")


def generate_report(
    threshold_path: Path = THRESHOLD_PATH,
    metrics_path: Path = METRICS_PATH,
) -> ScorecardArtifacts:
    thresholds_raw = load_json(threshold_path, "thresholds")
    metrics_raw = load_json(metrics_path, "metrics")
    results = evaluate_metrics(thresholds_raw, metrics_raw)
    status = compute_status(results)
    timestamp = isoformat_utc()
    thresholds_version = int(thresholds_raw["version"])
    metrics_version = int(metrics_raw["version"])
    report: Dict[str, Any] = {
        "schema_version": SCHEMA_VERSION,
        "timestamp_utc": timestamp,
        "status": status,
        "metrics": {
            result.spec.key: {
                "observed": result.observed_for_json(),
                "target": result.target_for_json(),
                "ok": result.ok,
            }
            for result in results
        },
        "inputs": {
            "thresholds": {
                "version": thresholds_version,
                "timestamp_utc": thresholds_raw["timestamp_utc"],
            },
            "metrics": {
                "version": metrics_version,
                "timestamp_utc": metrics_raw["timestamp_utc"],
            },
        },
    }
    bundle_payload = canonical_dumps(thresholds_raw) + canonical_dumps(metrics_raw)
    bundle_hash = hashlib.sha256(bundle_payload.encode("utf-8")).hexdigest()
    report["bundle"] = {"sha256": bundle_hash}
    write_outputs(report, results, bundle_hash, thresholds_version, metrics_version)
    return ScorecardArtifacts(
        report=report,
        results=results,
        bundle_sha256=bundle_hash,
        thresholds_version=thresholds_version,
        metrics_version=metrics_version,
    )


def main() -> int:
    try:
        artifacts = generate_report()
    except ScorecardError as exc:
        print(f"FAIL {exc}")
        ensure_output_dir()
        (OUTPUT_DIR / "guard_status.txt").write_text("FAIL
", encoding="utf-8")
        return 1
    else:
        print(f"{artifacts.report['status']} Sprint 6 scorecards")
        return 0


if __name__ == "__main__":
    raise SystemExit(main())
