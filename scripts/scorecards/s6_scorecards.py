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

import jsonschema  # noqa: E402

getcontext().prec = 28
getcontext().rounding = ROUND_HALF_EVEN

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
class MetricSpec:
    key: str
    label: str
    threshold_key: str
    comparison: str
    quantize: Decimal
    markdown_suffix: str = ""


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
    ),
    MetricSpec(
        key="failover_time_p95_s",
        label="Failover Time p95 (s)",
        threshold_key="failover_time_p95_s_max",
        comparison="lte",
        quantize=Decimal("0.001"),
        markdown_suffix="s",
    ),
    MetricSpec(
        key="staleness_p95_s",
        label="Staleness p95 (s)",
        threshold_key="staleness_p95_s_max",
        comparison="lte",
        quantize=Decimal("0.001"),
        markdown_suffix="s",
    ),
    MetricSpec(
        key="cdc_lag_p95_s",
        label="CDC Lag p95 (s)",
        threshold_key="cdc_lag_p95_s_max",
        comparison="lte",
        quantize=Decimal("0.001"),
        markdown_suffix="s",
    ),
    MetricSpec(
        key="divergence_pct",
        label="Divergence (%)",
        threshold_key="divergence_pct_max",
        comparison="lte",
        quantize=Decimal("0.1"),
        markdown_suffix="%",
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


def fail(code: str, message: str) -> None:
    raise ScorecardError(f"{ERROR_PREFIX}-E-{code}", message)


def load_json(path: Path, schema_key: str) -> Dict[str, object]:
    if not path.exists():
        fail("MISSING", f"Arquivo obrigatório ausente: {path}")
    try:
        content = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        fail("INVALID-JSON", f"Falha ao decodificar {path}: {exc}")
    schema_path = SCHEMA_FILES[schema_key]
    schema = json.loads(schema_path.read_text(encoding="utf-8"))
    try:
        jsonschema.validate(instance=content, schema=schema)
    except jsonschema.ValidationError as exc:
        fail("SCHEMA", f"Violação de schema em {path}: {exc.message}")
    return content


def decimal_from(value: object) -> Decimal:
    if isinstance(value, Decimal):
        return value
    if isinstance(value, (int, float, str)):
        try:
            return Decimal(str(value))
        except Exception as exc:  # pragma: no cover
            fail("DECIMAL", f"Valor inválido para Decimal: {value} ({exc})")
    fail("DECIMAL", f"Valor não numérico: {value}")


def evaluate_metrics(thresholds: Dict[str, object], metrics: Dict[str, object]) -> List[MetricResult]:
    results: List[MetricResult] = []
    for spec in METRIC_SPECS:
        observed = decimal_from(metrics[spec.key])
        target = decimal_from(thresholds[spec.threshold_key])
        if spec.comparison == "gte":
            ok = observed + EPSILON >= target
        else:
            ok = observed - EPSILON <= target
        results.append(MetricResult(spec=spec, observed=observed, target=target, ok=bool(ok)))
    return results


def compute_status(results: List[MetricResult]) -> str:
    return "PASS" if all(result.ok for result in results) else "FAIL"


def isoformat_utc() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def canonical_dumps(data: Dict[str, object]) -> str:
    return json.dumps(data, sort_keys=True, ensure_ascii=False, separators=(",", ":")) + "\n"


def ensure_output_dir() -> None:
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)


def render_markdown(
    report: Dict[str, object],
    results: List[MetricResult],
    bundle_sha256: str,
    thresholds_version: int,
    metrics_version: int,
) -> str:
    status = report["status"]
    emoji = "✅" if status == "PASS" else "❌"
    lines = ["# Sprint 6 Scorecards", ""]
    lines.append(f"{emoji} Status geral: **{status}**")
    lines.append("")
    lines.append(f"- Timestamp UTC: {report['timestamp_utc']}")
    lines.append(f"- Versão dos thresholds: {thresholds_version}")
    lines.append(f"- Versão das métricas: {metrics_version}")
    lines.append(f"- SHA do bundle: `{bundle_sha256}`")
    lines.append("")
    lines.append("| Métrica | Observado | Alvo | Status |")
    lines.append("| --- | --- | --- | --- |")
    for result in results:
        emoji_metric = "✅" if result.ok else "❌"
        lines.append(
            f"| {result.spec.label} | {result.formatted_observed()} | {result.formatted_target()} | "
            f"{emoji_metric} {result.status_text()} |"
        )
    lines.append("")
    lines.append("## O que fazer agora")
    failing = [result for result in results if not result.ok]
    if failing:
        for result in failing:
            lines.append(f"- {result.spec.label}: executar runbook de correção e revisar telemetria.")
    else:
        lines.append("- Todas as métricas passaram. Manter monitoramento em 24h.")
    lines.append("")
    return "\n".join(lines) + "\n"


def build_pr_comment(report: Dict[str, object], results: List[MetricResult], bundle_sha256: str) -> str:
    status = report["status"]
    emoji = "✅" if status == "PASS" else "❌"
    lines = [f"{emoji} [Sprint 6 report](./report.md)"]
    lines.append("")
    lines.append("![Status](./badge.svg)")
    lines.append("")
    lines.append("## O que fazer agora")
    failing = [result for result in results if not result.ok]
    if failing:
        for result in failing:
            lines.append(f"- {result.spec.label}: executar runbook de correção e revisar telemetria.")
    else:
        lines.append("- Nenhuma ação imediata necessária.")
    lines.append("")
    lines.append(f"Bundle SHA-256: `{bundle_sha256}`")
    lines.append("")
    lines.append("Relatório completo disponível em [report.md](./report.md).")
    return "\n".join(lines) + "\n"


def render_svg_badge(status: str) -> str:
    color = "#2e8540" if status == "PASS" else "#c92a2a"
    return (
        "<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"160\" height=\"40\">"
        f"<rect width=\"160\" height=\"40\" fill=\"{color}\" rx=\"6\"/>"
        "<text x=\"80\" y=\"25\" text-anchor=\"middle\" fill=\"#ffffff\" font-size=\"20\""
        " font-family=\"Helvetica,Arial,sans-serif\">S6 {status}</text>"
        "</svg>"
    )


def render_scorecard_svg(status: str, results: List[MetricResult]) -> str:
    rows = len(results)
    height = 60 + 30 * rows
    header = (
        f"<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"520\" height=\"{height}\">"
        "<style>text{font-family:Helvetica,Arial,sans-serif;font-size:14px;}</style>"
        "<rect width=\"520\" height=\"{height}\" fill=\"#ffffff\" stroke=\"#1f2933\" rx=\"8\"/>"
        "<text x=\"20\" y=\"30\" font-size=\"18\" font-weight=\"bold\">Sprint 6 Scorecards</text>"
        f"<text x=\"420\" y=\"30\" text-anchor=\"end\" font-size=\"16\">Status: {status}</text>"
    )
    lines = [header]
    y = 60
    for result in results:
        status_color = "#2e8540" if result.ok else "#c92a2a"
        lines.append(
            f"<text x=\"20\" y=\"{y}\">{result.spec.label}</text>"
            f"<text x=\"260\" y=\"{y}\">{result.formatted_observed()}</text>"
            f"<text x=\"370\" y=\"{y}\">{result.formatted_target()}</text>"
            f"<text x=\"460\" y=\"{y}\" fill=\"{status_color}\">{result.status_text()}</text>"
        )
        y += 30
    lines.append("</svg>")
    return "".join(lines)


def write_outputs(
    report: Dict[str, object],
    results: List[MetricResult],
    bundle_sha256: str,
    thresholds_version: int,
    metrics_version: int,
) -> None:
    ensure_output_dir()
    (OUTPUT_DIR / "report.json").write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    markdown = render_markdown(report, results, bundle_sha256, thresholds_version, metrics_version)
    (OUTPUT_DIR / "report.md").write_text(markdown, encoding="utf-8")
    pr_comment = build_pr_comment(report, results, bundle_sha256)
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
    timestamp = isoformat_utc()
    report = {
        "schema_version": 1,
        "timestamp_utc": timestamp,
        "status": compute_status(results),
        "metrics": {
            result.spec.key: {
                "observed": result.observed_for_json(),
                "target": result.target_for_json(),
                "ok": result.ok,
            }
            for result in results
        },
    }
    bundle_payload = canonical_dumps(thresholds_raw) + canonical_dumps(metrics_raw)
    bundle_hash = hashlib.sha256(bundle_payload.encode("utf-8")).hexdigest()
    write_outputs(
        report,
        results,
        bundle_hash,
        int(thresholds_raw["version"]),
        int(metrics_raw["version"]),
    )
    return ScorecardArtifacts(
        report=report,
        results=results,
        bundle_sha256=bundle_hash,
        thresholds_version=int(thresholds_raw["version"]),
        metrics_version=int(metrics_raw["version"]),
    )


def main() -> int:
    try:
        artifacts = generate_report()
    except ScorecardError as exc:
        print(f"FAIL {exc}")
        ensure_output_dir()
        (OUTPUT_DIR / "guard_status.txt").write_text("FAIL\n", encoding="utf-8")
        return 1
    else:
        status = artifacts.report["status"]
        prefix = "PASS" if status == "PASS" else "FAIL"
        print(f"{prefix} Sprint 6 scorecards")
        return 0


if __name__ == "__main__":
    raise SystemExit(main())
