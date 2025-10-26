#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass
from datetime import datetime, timezone
from decimal import Decimal, ROUND_HALF_EVEN, getcontext
from pathlib import Path
from typing import Dict, List, Tuple

import sys

BASE_DIR = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(BASE_DIR))

import jsonschema
THRESHOLDS_PATH = BASE_DIR / "s6_validation" / "thresholds.json"
METRICS_PATH = BASE_DIR / "s6_validation" / "metrics_static.json"
SCHEMA_FILES = {
    "thresholds": BASE_DIR / "schemas" / "thresholds.schema.json",
    "metrics": BASE_DIR / "schemas" / "metrics.schema.json",
    "report": BASE_DIR / "schemas" / "report.schema.json",
}
OUTPUT_DIR = BASE_DIR / "out" / "s6_scorecards"
ERROR_PREFIX = "S6"

getcontext().prec = 28
getcontext().rounding = ROUND_HALF_EVEN
EPSILON = Decimal("1e-12")


@dataclass(frozen=True)
class MetricSpec:
    key: str
    label: str
    comparison: str
    quantize: Decimal
    markdown_suffix: str = ""


@dataclass(frozen=True)
class MetricResult:
    spec: MetricSpec
    observed: Decimal
    target: Decimal
    ok: bool

    def observed_for_json(self) -> float:
        return float(self.observed.quantize(self.spec.quantize))

    def target_for_json(self) -> float:
        return float(self.target.quantize(self.spec.quantize))

    def formatted_observed(self) -> str:
        value = self.observed.quantize(self.spec.quantize)
        text = format(value, "f")
        return text + self.spec.markdown_suffix

    def formatted_target(self) -> str:
        value = self.target.quantize(self.spec.quantize)
        text = format(value, "f")
        return text + self.spec.markdown_suffix

    def status_text(self) -> str:
        return "PASS" if self.ok else "FAIL"


METRIC_SPECS: List[MetricSpec] = [
    MetricSpec(
        key="quorum_ratio",
        label="Quorum Ratio",
        comparison="gte",
        quantize=Decimal("0.0001"),
    ),
    MetricSpec(
        key="failover_time_p95_s",
        label="Failover Time p95 (s)",
        comparison="lte",
        quantize=Decimal("0.001"),
    ),
    MetricSpec(
        key="staleness_p95_s",
        label="Staleness p95 (s)",
        comparison="lte",
        quantize=Decimal("0.001"),
    ),
    MetricSpec(
        key="cdc_lag_p95_s",
        label="CDC Lag p95 (s)",
        comparison="lte",
        quantize=Decimal("0.001"),
    ),
    MetricSpec(
        key="divergence_pct",
        label="Divergence (%)",
        comparison="lte",
        quantize=Decimal("0.1"),
        markdown_suffix="%",
    ),
]


def fail(code: str, message: str) -> None:
    raise RuntimeError(f"{ERROR_PREFIX}-E-{code}:{message}")


def load_json(path: Path, schema_key: str) -> Dict[str, object]:
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


def extract_threshold_targets(data: Dict[str, object]) -> Tuple[Dict[str, Decimal], Dict[str, int]]:
    metrics_section = data.get("metrics")
    if not isinstance(metrics_section, dict):
        fail("THRESHOLDS", "Bloco metrics ausente em thresholds.json")
    targets: Dict[str, Decimal] = {}
    versions: Dict[str, int] = {}
    for spec in METRIC_SPECS:
        payload = metrics_section.get(spec.key)
        if not isinstance(payload, dict):
            fail("MISSING-THRESHOLD", f"Payload ausente para {spec.key}")
        comparison = payload.get("comparison")
        if comparison != spec.comparison:
            fail("COMPARISON", f"Comparador inválido para {spec.key}: {comparison}")
        version_value = payload.get("version")
        if not isinstance(version_value, int):
            fail("VERSION", f"Versão inválida em thresholds para {spec.key}")
        if "target" not in payload:
            fail("TARGET", f"Target ausente para {spec.key}")
        targets[spec.key] = decimal_from(payload["target"])
        versions[spec.key] = version_value
    return targets, versions


def extract_metric_observations(data: Dict[str, object]) -> Tuple[Dict[str, Decimal], Dict[str, int]]:
    metrics_section = data.get("metrics")
    if not isinstance(metrics_section, dict):
        fail("METRICS", "Bloco metrics ausente em metrics_static.json")
    observations: Dict[str, Decimal] = {}
    versions: Dict[str, int] = {}
    for spec in METRIC_SPECS:
        payload = metrics_section.get(spec.key)
        if not isinstance(payload, dict):
            fail("MISSING-METRIC", f"Payload ausente para {spec.key}")
        version_value = payload.get("version")
        if not isinstance(version_value, int):
            fail("VERSION", f"Versão inválida em metrics para {spec.key}")
        if "observed" not in payload:
            fail("OBSERVED", f"Valor observado ausente para {spec.key}")
        observations[spec.key] = decimal_from(payload["observed"])
        versions[spec.key] = version_value
    return observations, versions


def compare(observed: Decimal, target: Decimal, comparison: str) -> bool:
    if comparison == "gte":
        return observed + EPSILON >= target
    if comparison == "lte":
        return observed - EPSILON <= target
    fail("COMPARISON", f"Operador desconhecido: {comparison}")
    return False


def evaluate_metrics(targets: Dict[str, Decimal], observations: Dict[str, Decimal]) -> List[MetricResult]:
    results: List[MetricResult] = []
    for spec in METRIC_SPECS:
        observed = observations[spec.key]
        target = targets[spec.key]
        ok = compare(observed, target, spec.comparison)
        results.append(MetricResult(spec=spec, observed=observed, target=target, ok=ok))
    return results


def compute_status(results: List[MetricResult]) -> str:
    return "PASS" if all(result.ok for result in results) else "FAIL"


def isoformat_utc() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def canonical_dumps(data: Dict[str, object]) -> str:
    return json.dumps(data, sort_keys=True, ensure_ascii=False, separators=(",", ":")) + "\n"


def compute_bundle_sha(thresholds_raw: Dict[str, object], metrics_raw: Dict[str, object]) -> str:
    payload = canonical_dumps(thresholds_raw) + canonical_dumps(metrics_raw)
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()


def build_report(
    results: List[MetricResult],
    generated_at: str,
    thresholds_raw: Dict[str, object],
    thresholds_versions: Dict[str, int],
    metrics_raw: Dict[str, object],
    metrics_versions: Dict[str, int],
    bundle_hash: str,
) -> Dict[str, object]:
    metrics_block = {
        spec.key: {
            "observed": result.observed_for_json(),
            "target": result.target_for_json(),
            "ok": result.ok,
        }
        for spec, result in zip(METRIC_SPECS, results)
    }
    thresholds_meta = {
        "version": int(thresholds_raw["version"]),
        "timestamp_utc": thresholds_raw["timestamp_utc"],
        "metrics": {
            spec.key: {
                "version": thresholds_versions[spec.key],
                "comparison": spec.comparison,
            }
            for spec in METRIC_SPECS
        },
    }
    metrics_meta = {
        "version": int(metrics_raw["version"]),
        "timestamp_utc": metrics_raw["timestamp_utc"],
        "metrics": {
            spec.key: {
                "version": metrics_versions[spec.key],
            }
            for spec in METRIC_SPECS
        },
    }
    return {
        "schema_version": 1,
        "timestamp_utc": generated_at,
        "status": compute_status(results),
        "metrics": metrics_block,
        "inputs": {
            "thresholds": thresholds_meta,
            "metrics": metrics_meta,
        },
        "bundle": {
            "sha256": bundle_hash,
        },
    }


def render_markdown(
    report: Dict[str, object],
    results: List[MetricResult],
    thresholds_raw: Dict[str, object],
    metrics_raw: Dict[str, object],
    bundle_sha256: str,
) -> str:
    status = report["status"]
    emoji = "✅" if status == "PASS" else "❌"
    lines = ["# Sprint 6 Scorecards", ""]
    lines.append(f"{emoji} Status geral: **{status}**")
    lines.append("")
    lines.append(f"- Relatório gerado em: {report['timestamp_utc']}")
    lines.append(
        f"- Thresholds: v{thresholds_raw['version']} @ {thresholds_raw['timestamp_utc']}"
    )
    lines.append(f"- Métricas: v{metrics_raw['version']} @ {metrics_raw['timestamp_utc']}")
    lines.append(f"- Bundle SHA-256: `{bundle_sha256}`")
    lines.append("")
    lines.append("| Métrica | Observado | Alvo | Status |")
    lines.append("| --- | --- | --- | --- |")
    for result in results:
        metric_emoji = "✅" if result.ok else "❌"
        lines.append(
            f"| {result.spec.label} | {result.formatted_observed()} | {result.formatted_target()} | "
            f"{metric_emoji} {result.status_text()} |"
        )
    lines.append("")
    lines.append("## Próximos passos")
    failing = [result for result in results if not result.ok]
    if failing:
        lines.append("- Investigar métricas reprovadas seguindo o runbook da Sprint 6.")
    else:
        lines.append("- Nenhuma ação imediata necessária; manter monitoramento de rotina.")
    lines.append("")
    return "\n".join(lines) + "\n"


def render_pr_comment(
    report: Dict[str, object],
    thresholds_raw: Dict[str, object],
    metrics_raw: Dict[str, object],
    bundle_sha256: str,
) -> str:
    status = report["status"]
    emoji = "✅" if status == "PASS" else "❌"
    lines = [f"{emoji} [Sprint 6 report](./report.md)", ""]
    lines.append("![Status](./badge.svg)")
    lines.append("")
    lines.append(
        f"- Thresholds: v{thresholds_raw['version']} @ {thresholds_raw['timestamp_utc']}"
    )
    lines.append(f"- Métricas: v{metrics_raw['version']} @ {metrics_raw['timestamp_utc']}")
    lines.append(f"- Bundle SHA-256: `{bundle_sha256}`")
    lines.append(f"- Gerado em: {report['timestamp_utc']}")
    lines.append("")
    lines.append("Relatório completo disponível em [report.md](./report.md).")
    lines.append("")
    return "\n".join(lines) + "\n"


def render_svg_badge(status: str) -> str:
    color = "#2e8540" if status == "PASS" else "#c92a2a"
    return (
        "<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"150\" height=\"40\">"
        f"<rect width=\"150\" height=\"40\" rx=\"6\" fill=\"{color}\"/>"
        f"<text x=\"75\" y=\"25\" text-anchor=\"middle\" fill=\"#ffffff\" font-size=\"18\""
        f" font-family=\"Helvetica,Arial,sans-serif\">S6 {status}</text>"
        "</svg>"
    )


def render_scorecard_svg(results: List[MetricResult]) -> str:
    rows = len(results)
    height = 70 + rows * 30
    status = compute_status(results)
    header = (
        f"<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"520\" height=\"{height}\">"
        "<style>text{font-family:Helvetica,Arial,sans-serif;font-size:14px;}</style>"
        f"<rect width=\"520\" height=\"{height}\" fill=\"#ffffff\" stroke=\"#1f2933\" rx=\"8\"/>"
        "<text x=\"20\" y=\"30\" font-size=\"18\" font-weight=\"bold\">Sprint 6 Scorecards</text>"
        f"<text x=\"500\" y=\"30\" text-anchor=\"end\" font-size=\"16\">Status: {status}</text>"
        "<text x=\"20\" y=\"50\" font-weight=\"bold\">Métrica</text>"
        "<text x=\"250\" y=\"50\" font-weight=\"bold\">Observado</text>"
        "<text x=\"360\" y=\"50\" font-weight=\"bold\">Alvo</text>"
        "<text x=\"460\" y=\"50\" font-weight=\"bold\">Status</text>"
    )
    lines = [header]
    y = 80
    for result in results:
        status_color = "#2e8540" if result.ok else "#c92a2a"
        lines.append(
            f"<text x=\"20\" y=\"{y}\">{result.spec.label}</text>"
            f"<text x=\"250\" y=\"{y}\">{result.formatted_observed()}</text>"
            f"<text x=\"360\" y=\"{y}\">{result.formatted_target()}</text>"
            f"<text x=\"460\" y=\"{y}\" fill=\"{status_color}\">{result.status_text()}</text>"
        )
        y += 30
    lines.append("</svg>")
    return "".join(lines)


def ensure_output_dir() -> None:
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)


def write_outputs(
    report: Dict[str, object],
    results: List[MetricResult],
    thresholds_raw: Dict[str, object],
    metrics_raw: Dict[str, object],
    bundle_sha256: str,
) -> None:
    ensure_output_dir()
    (OUTPUT_DIR / "report.json").write_text(
        json.dumps(report, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    markdown = render_markdown(report, results, thresholds_raw, metrics_raw, bundle_sha256)
    (OUTPUT_DIR / "report.md").write_text(markdown, encoding="utf-8")
    pr_comment = render_pr_comment(report, thresholds_raw, metrics_raw, bundle_sha256)
    (OUTPUT_DIR / "pr_comment.md").write_text(pr_comment, encoding="utf-8")
    badge_svg = render_svg_badge(report["status"])
    (OUTPUT_DIR / "badge.svg").write_text(badge_svg + "\n", encoding="utf-8")
    scorecard_svg = render_scorecard_svg(results)
    (OUTPUT_DIR / "scorecard.svg").write_text(scorecard_svg + "\n", encoding="utf-8")
    (OUTPUT_DIR / "guard_status.txt").write_text(report["status"] + "\n", encoding="utf-8")
    (OUTPUT_DIR / "bundle.sha256").write_text(bundle_sha256 + "\n", encoding="utf-8")


def validate_report_schema(report: Dict[str, object]) -> None:
    schema_path = SCHEMA_FILES["report"]
    schema = json.loads(schema_path.read_text(encoding="utf-8"))
    try:
        jsonschema.validate(instance=report, schema=schema)
    except jsonschema.ValidationError as exc:
        fail("REPORT-SCHEMA", f"Violação de schema em report.json: {exc.message}")


def generate_report(
    threshold_path: Path = THRESHOLDS_PATH,
    metrics_path: Path = METRICS_PATH,
) -> Dict[str, object]:
    thresholds_raw = load_json(threshold_path, "thresholds")
    metrics_raw = load_json(metrics_path, "metrics")
    targets, threshold_versions = extract_threshold_targets(thresholds_raw)
    observations, metric_versions = extract_metric_observations(metrics_raw)
    results = evaluate_metrics(targets, observations)
    generated_at = isoformat_utc()
    bundle_hash = compute_bundle_sha(thresholds_raw, metrics_raw)
    report = build_report(
        results,
        generated_at,
        thresholds_raw,
        threshold_versions,
        metrics_raw,
        metric_versions,
        bundle_hash,
    )
    validate_report_schema(report)
    write_outputs(report, results, thresholds_raw, metrics_raw, bundle_hash)
    return report


def main() -> int:
    try:
        report = generate_report()
    except RuntimeError as exc:
        print(f"FAIL {exc}")
        ensure_output_dir()
        (OUTPUT_DIR / "guard_status.txt").write_text("FAIL\n", encoding="utf-8")
        return 1
    else:
        print(f"{report['status']} Sprint 6 scorecards")
        return 0


if __name__ == "__main__":
    raise SystemExit(main())
