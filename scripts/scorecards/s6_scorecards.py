#!/usr/bin/env python3
"""Generate deterministic Sprint 6 scorecards."""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from dataclasses import dataclass
from datetime import datetime, timezone
from decimal import Decimal, ROUND_HALF_EVEN, getcontext
from pathlib import Path
from typing import Dict, Iterable, List, Sequence

import jsonschema

BASE_DIR = Path(__file__).resolve().parents[2]
SCHEMAS_DIR = BASE_DIR / "schemas"
THRESHOLDS_PATH = BASE_DIR / "s6_validation" / "thresholds.json"
METRICS_PATH = BASE_DIR / "s6_validation" / "metrics_static.json"
OUTPUT_DIR = BASE_DIR / "out" / "s6_scorecards"

SCHEMA_FILES: Dict[str, Path] = {
    "thresholds": SCHEMAS_DIR / "thresholds.schema.json",
    "metrics": SCHEMAS_DIR / "metrics.schema.json",
    "report": SCHEMAS_DIR / "report.schema.json",
}

REPORT_SCHEMA = "trendmarketv2.sprint6.report"
SCHEMA_VERSION = 2
ERROR_PREFIX = "S6"
EPSILON = Decimal("1e-12")

getcontext().prec = 28
getcontext().rounding = ROUND_HALF_EVEN


class ScorecardError(RuntimeError):
    """Raised for deterministic scorecard failures."""

    def __init__(self, code: str, message: str) -> None:
        self.code = f"{ERROR_PREFIX}-E-{code}"
        super().__init__(f"{self.code}:{message}")


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
    delta: Decimal
    sample_size: int
    window: str
    guidance: str = ""

    def formatted_observed(self) -> str:
        return format_value(self.observed, self.definition.unit)

    def formatted_target(self) -> str:
        return format_value(self.target, self.definition.unit)


@dataclass(frozen=True)
class ScorecardArtifacts:
    report: Dict[str, object]
    results: List[MetricResult]
    bundle_sha256: str
    thresholds: Dict[str, object]
    metrics: Dict[str, object]


METRIC_DEFINITIONS: Sequence[MetricDefinition] = (
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
        label="Replica staleness p95 (s)",
        comparator="lte",
        unit="seconds",
        quantize=Decimal("0.001"),
    ),
    MetricDefinition(
        key="cdc_lag_p95_s",
        label="CDC lag p95 (s)",
        comparator="lte",
        unit="seconds",
        quantize=Decimal("0.001"),
    ),
    MetricDefinition(
        key="divergence_pct",
        label="Oracle divergence (%)",
        comparator="lte",
        unit="percent",
        quantize=Decimal("0.1"),
    ),
)


_schema_cache: Dict[str, Dict[str, object]] = {}


def isoformat_utc() -> str:
    return (
        datetime.now(timezone.utc)
        .replace(microsecond=0)
        .isoformat()
        .replace("+00:00", "Z")
    )


def canonical_dumps(payload: Dict[str, object]) -> str:
    return json.dumps(
        payload, sort_keys=True, ensure_ascii=False, separators=(",", ":")
    )


def load_schema(schema_key: str) -> Dict[str, object]:
    try:
        return _schema_cache[schema_key]
    except KeyError:
        path = SCHEMA_FILES[schema_key]
        try:
            data = json.loads(path.read_text(encoding="utf-8"))
        except FileNotFoundError as exc:
            raise ScorecardError("SCHEMA-MISSING", f"Schema ausente: {path}") from exc
        _schema_cache[schema_key] = data
        return data


def load_json(path: Path, schema_key: str) -> Dict[str, object]:
    try:
        raw = path.read_text(encoding="utf-8")
    except FileNotFoundError as exc:
        raise ScorecardError("MISSING", f"Arquivo obrigatório ausente: {path}") from exc
    except UnicodeDecodeError as exc:
        raise ScorecardError(
            "ENCODING", f"Codificação inválida em {path}: {exc}"
        ) from exc
    try:
        payload = json.loads(raw)
    except json.JSONDecodeError as exc:
        raise ScorecardError("INVALID", f"JSON inválido em {path}: {exc}") from exc
    schema = load_schema(schema_key)
    try:
        jsonschema.validate(instance=payload, schema=schema)
    except jsonschema.ValidationError as exc:
        raise ScorecardError(
            "SCHEMA", f"Violação de schema em {path}: {exc.message}"
        ) from exc
    return payload


def as_decimal(value: object, *, field: str) -> Decimal:
    try:
        return Decimal(str(value))
    except Exception as exc:  # pragma: no cover - defensive
        raise ScorecardError(
            "DECIMAL", f"Valor inválido para {field}: {value}"
        ) from exc


def compare_values(
    comparator: str, observed: Decimal, target: Decimal
) -> tuple[bool, Decimal]:
    if comparator == "gte":
        delta = observed - target
        return observed + EPSILON >= target, delta
    if comparator == "lte":
        delta = target - observed
        return observed - EPSILON <= target, delta
    raise ScorecardError("COMPARATOR", f"Comparador desconhecido: {comparator}")


def evaluate_metrics(
    thresholds: Dict[str, object], metrics: Dict[str, object]
) -> List[MetricResult]:
    results: List[MetricResult] = []
    for definition in METRIC_DEFINITIONS:
        threshold_value = thresholds.get(definition.key)
        metric_payload = metrics.get(definition.key)
        if threshold_value is None or metric_payload is None:
            raise ScorecardError("SCHEMA", f"Métrica ausente: {definition.key}")
        target = as_decimal(threshold_value, field=f"thresholds.{definition.key}")
        observed = as_decimal(
            metric_payload["observed"], field=f"metrics.{definition.key}.observed"
        )
        ok, delta = compare_values(definition.comparator, observed, target)
        guidance = str(metric_payload.get("guidance", ""))
        result = MetricResult(
            definition=definition,
            observed=observed.quantize(definition.quantize),
            target=target.quantize(definition.quantize),
            ok=ok,
            delta=delta.quantize(definition.quantize),
            sample_size=int(metric_payload["sample_size"]),
            window=str(metric_payload["window"]),
            guidance=guidance,
        )
        results.append(result)
    return results


def compute_summary(results: Iterable[MetricResult]) -> Dict[str, int]:
    total = 0
    passing = 0
    for result in results:
        total += 1
        if result.ok:
            passing += 1
    return {"total": total, "passing": passing, "failing": total - passing}


def format_value(value: Decimal, unit: str) -> str:
    if unit == "ratio":
        return f"{value.quantize(Decimal('0.0001'))}"
    if unit == "seconds":
        return f"{value.quantize(Decimal('0.001'))}s"
    if unit == "percent":
        return f"{value.quantize(Decimal('0.1'))}%"
    return str(value)


def compute_bundle_sha(
    thresholds: Dict[str, object], metrics: Dict[str, object]
) -> str:
    material = canonical_dumps(thresholds) + "\n" + canonical_dumps(metrics) + "\n"
    return hashlib.sha256(material.encode("utf-8")).hexdigest()


def build_report(
    *,
    generated_at: str,
    results: List[MetricResult],
    thresholds: Dict[str, object],
    metrics: Dict[str, object],
    bundle_sha: str,
) -> Dict[str, object]:
    summary = compute_summary(results)
    status = "PASS" if summary["failing"] == 0 else "FAIL"
    metrics_block: Dict[str, Dict[str, object]] = {}
    for result in results:
        metrics_block[result.definition.key] = {
            "observed": str(result.observed),
            "target": str(result.target),
            "delta": str(result.delta),
            "comparison": result.definition.comparator,
            "unit": result.definition.unit,
            "sample_size": result.sample_size,
            "window": result.window,
            "ok": result.ok,
            "formatted_observed": result.formatted_observed(),
            "formatted_target": result.formatted_target(),
            "guidance": result.guidance or "",
        }
    report = {
        "schema": REPORT_SCHEMA,
        "schema_version": SCHEMA_VERSION,
        "timestamp_utc": generated_at,
        "status": status,
        "summary": summary,
        "metrics": metrics_block,
        "inputs": {
            "thresholds": thresholds,
            "metrics": metrics,
        },
        "bundle": {"sha256": bundle_sha},
    }
    schema = load_schema("report")
    jsonschema.validate(instance=report, schema=schema)
    return report


def render_markdown(artifacts: ScorecardArtifacts) -> str:
    lines = ["# Sprint 6 Scorecard", ""]
    emoji = "✅" if artifacts.report["status"] == "PASS" else "❌"
    lines.append(f"{emoji} Status geral: **{artifacts.report['status']}**")
    lines.append("")
    lines.append("| Métrica | Observado | Meta | Status |")
    lines.append("| --- | --- | --- | --- |")
    for result in artifacts.results:
        status_icon = "✅" if result.ok else "❌"
        lines.append(
            "| {label} | {observed} | {target} | {status_icon} {status} |".format(
                label=result.definition.label,
                observed=result.formatted_observed(),
                target=result.formatted_target(),
                status_icon=status_icon,
                status="PASS" if result.ok else "FAIL",
            )
        )
    lines.append("")
    lines.append("## Entradas")
    lines.append(f"- Thresholds: `{artifacts.thresholds['timestamp_utc']}`")
    lines.append(f"- Métricas: `{artifacts.metrics['timestamp_utc']}`")
    lines.append(f"- Bundle SHA256: `{artifacts.bundle_sha256}`")
    return "\n".join(lines) + "\n"


def render_pr_comment(artifacts: ScorecardArtifacts) -> str:
    emoji = "✅" if artifacts.report["status"] == "PASS" else "❌"
    lines = [f"{emoji} [Sprint 6 report](./report.md)", ""]
    lines.append("![Status](./badge.svg)")
    lines.append("")
    lines.append("Resumo:")
    for result in artifacts.results:
        status_icon = "✅" if result.ok else "❌"
        lines.append(
            f"- {status_icon} {result.definition.label}: {result.formatted_observed()} (meta {result.formatted_target()})"
        )
    lines.append("")
    lines.append(f"Bundle SHA256: `{artifacts.bundle_sha256}`")
    return "\n".join(lines) + "\n"


def render_badge(status: str) -> str:
    color = "4c9a2a" if status == "PASS" else "cc3300"
    return (
        '<svg xmlns="http://www.w3.org/2000/svg" width="180" height="40">'
        f'<rect width="180" height="40" rx="6" fill="#{color}"/>'
        f'<text x="90" y="25" text-anchor="middle" fill="#ffffff" font-size="20"'
        ' font-family="Helvetica,Arial,sans-serif">Sprint 6 {status}</text>'.format(
            status=status
        )
        + "</svg>"
    )


def ensure_output_dir() -> None:
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)


def write_outputs(artifacts: ScorecardArtifacts) -> None:
    ensure_output_dir()
    (OUTPUT_DIR / "report.json").write_text(
        json.dumps(artifacts.report, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    (OUTPUT_DIR / "report.md").write_text(render_markdown(artifacts), encoding="utf-8")
    (OUTPUT_DIR / "pr_comment.md").write_text(
        render_pr_comment(artifacts), encoding="utf-8"
    )
    (OUTPUT_DIR / "guard_status.txt").write_text(
        f"{artifacts.report['status']}\n", encoding="utf-8"
    )
    (OUTPUT_DIR / "bundle.sha256").write_text(
        f"{artifacts.bundle_sha256}\n", encoding="utf-8"
    )
    (OUTPUT_DIR / "badge.svg").write_text(
        render_badge(str(artifacts.report["status"])) + "\n", encoding="utf-8"
    )


def generate_report(
    *,
    threshold_path: Path = THRESHOLDS_PATH,
    metrics_path: Path = METRICS_PATH,
) -> ScorecardArtifacts:
    thresholds_payload = load_json(threshold_path, "thresholds")
    metrics_payload = load_json(metrics_path, "metrics")
    results = evaluate_metrics(thresholds_payload, metrics_payload)
    generated_at = isoformat_utc()
    bundle_sha = compute_bundle_sha(thresholds_payload, metrics_payload)
    report = build_report(
        generated_at=generated_at,
        results=results,
        thresholds=thresholds_payload,
        metrics=metrics_payload,
        bundle_sha=bundle_sha,
    )
    artifacts = ScorecardArtifacts(
        report=report,
        results=results,
        bundle_sha256=bundle_sha,
        thresholds=thresholds_payload,
        metrics=metrics_payload,
    )
    write_outputs(artifacts)
    return artifacts


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Execute Sprint 6 deterministic scorecards"
    )
    parser.add_argument(
        "--thresholds",
        type=Path,
        default=THRESHOLDS_PATH,
        help="Caminho para thresholds.json",
    )
    parser.add_argument(
        "--metrics", type=Path, default=METRICS_PATH, help="Caminho para metrics.json"
    )
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv or sys.argv[1:])
    artifacts = generate_report(
        threshold_path=args.thresholds, metrics_path=args.metrics
    )
    return 0 if artifacts.report["status"] == "PASS" else 1


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main(sys.argv[1:]))
