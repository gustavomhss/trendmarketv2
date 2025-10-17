#!/usr/bin/env python3
import json
import os
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "src"
if str(SRC) not in sys.path:
    sys.path.insert(0, str(SRC))

from amm_obs import AMMObservability  # noqa: E402

EVIDENCE = ROOT / "out" / "obs_gatecheck" / "evidence"
EVIDENCE.mkdir(parents=True, exist_ok=True)

OUTPUT_JSON = EVIDENCE / "costs_cardinality.json"
OPS_DIR = ROOT / "ops" / "obs"
OPS_DIR.mkdir(parents=True, exist_ok=True)
OUTPUT_MD = OPS_DIR / "costs_cardinality.md"

obs = AMMObservability(
    env=os.getenv("OBS_ENV", "dev"),
    service=os.getenv("OBS_SERVICE", "trendmarket-amm"),
    version=os.getenv("OBS_VERSION", "v0.1.0"),
    observability_level="full",
)

report = obs.cardinality_breakdown()
OUTPUT_JSON.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")

violations = [
    metric
    for metric, payload in report.get("metrics", {}).items()
    if payload.get("ratio") is not None and payload["ratio"] >= 0.7
]
if violations:
    print("CARDINALITY_BUDGET_FAIL:", ", ".join(sorted(violations)))
    sys.exit(1)

lines = [
    "# Observability Cost & Cardinality",
    "",
    "| Metric | Series | Budget | Usage % | Est. USD/mo |",
    "| --- | ---: | ---: | ---: | ---: |",
]
for metric, payload in sorted(report["metrics"].items()):
    series = payload.get("series", 0)
    budget = payload.get("budget") or 0
    ratio = payload.get("ratio")
    cost = payload.get("est_usd_month", 0.0)
    usage_pct = f"{ratio * 100:.1f}%" if ratio is not None else "n/a"
    lines.append(
        f"| `{metric}` | {series:.0f} | {budget:.0f} | {usage_pct} | ${cost:.2f} |"
    )

lines.extend(
    [
        "",
        f"**Preço por milhão de amostras:** ${report['price_per_million_samples']:.2f}",
        f"**Retenção (dias):** {report['retention_days']}",
        f"**Intervalo de scrape (s):** {report['scrape_interval_seconds']}",
        "",
        f"**Custo estimado mensal:** ${report['total_estimated_usd_month']:.2f}",
    ]
)

OUTPUT_MD.write_text("\n".join(lines) + "\n", encoding="utf-8")

print("COSTS_OK")
