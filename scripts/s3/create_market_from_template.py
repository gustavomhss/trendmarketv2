#!/usr/bin/env python3
"""Create a market from template with validation and telemetry."""

from __future__ import annotations

import json
import os
import sys
import time
import uuid
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from _telemetry import AuditLog, TelemetryEmitter, ensure_evidence_dir  # noqa: E402
from _yaml import load as yaml_load  # noqa: E402

CAT_PATH = Path(os.getenv("MBP_TEMPLATE_CATALOG", "configs/templates/catalog.json"))
POLICY_PATH = Path(os.getenv("MBP_POLICY_FILE", "configs/policies/mbp_s3.yml"))
GENERATED = Path(
    os.getenv("MBP_GENERATED_MARKETS", "out/s3_gatecheck/generated_markets.json")
)
AUDIT_LOG = AuditLog("market_created_template")
TELEMETRY = TelemetryEmitter("market_created_template")


@dataclass
class Template:
    id: str
    category: str
    truth_source: str
    min_liquidity: float
    resolution_window_h: int

    @classmethod
    def from_dict(cls, data: Dict[str, Any]) -> "Template":
        return cls(
            id=str(data["id"]),
            category=str(data["category"]),
            truth_source=str(data["truth_source"]),
            min_liquidity=float(data["min_liquidity"]),
            resolution_window_h=int(data["resolution_window_h"]),
        )


class Catalog:
    def __init__(self, raw: Dict[str, Any]):
        self.raw = raw
        self.templates = {
            tpl["id"]: Template.from_dict(tpl) for tpl in raw.get("templates", [])
        }
        self.validation = raw.get("validation", {})

    def get_template(self, tpl_id: str) -> Template:
        tpl = self.templates.get(tpl_id)
        if not tpl:
            raise ValueError(f"unknown template: {tpl_id}")
        return tpl

    def ensure_valid(self, tpl: Template) -> None:
        bounds = self.validation.get("min_liquidity_bounds", {}).get(tpl.category, {})
        min_bound = float(bounds.get("min", 0))
        max_bound = float(bounds.get("max", float("inf")))
        if tpl.min_liquidity < min_bound:
            raise ValueError(
                f"template {tpl.id} min_liquidity {tpl.min_liquidity} below minimum {min_bound}"
            )
        if tpl.min_liquidity > max_bound:
            raise ValueError(
                f"template {tpl.id} min_liquidity {tpl.min_liquidity} above maximum {max_bound}"
            )
        allowed_truth = self.validation.get("allowed_truth_sources", {}).get(
            tpl.category, []
        )
        if allowed_truth and tpl.truth_source not in allowed_truth:
            raise ValueError(
                f"template {tpl.id} truth_source {tpl.truth_source} not in allowed list {allowed_truth}"
            )
        window_cfg = self.validation.get("resolution_window_h", {})
        window_min = int(window_cfg.get("min", 1))
        window_max = int(window_cfg.get("max", 24 * 14))
        if tpl.resolution_window_h < window_min or tpl.resolution_window_h > window_max:
            raise ValueError(
                f"template {tpl.id} resolution_window_h {tpl.resolution_window_h} outside [{window_min}, {window_max}]"
            )


class Policy:
    def __init__(self, raw: Dict[str, Any]):
        self.raw = raw

    @property
    def template_creation_enabled(self) -> bool:
        feature_flags = self.raw.get("feature_flags", {})
        return bool(feature_flags.get("mbp.create.by_template", False))


def load_catalog() -> Catalog:
    data = json.loads(CAT_PATH.read_text(encoding="utf-8"))
    return Catalog(data)


def load_policy() -> Policy:
    raw = yaml_load(POLICY_PATH)
    raw = raw or {}
    return Policy(raw)


def validate_name(name: str) -> None:
    if not name or not name.strip():
        raise ValueError("market name must be non-empty")
    if len(name.strip()) < 4:
        raise ValueError("market name must have at least 4 characters")


def create_market(tpl: Template, name: str) -> Dict[str, Any]:
    now = int(time.time())
    deadline = now + tpl.resolution_window_h * 3600
    return {
        "market_id": str(uuid.uuid4()),
        "template_id": tpl.id,
        "name": name.strip(),
        "category": tpl.category,
        "truth_source": tpl.truth_source,
        "min_liquidity": tpl.min_liquidity,
        "resolution_deadline": deadline,
        "status": "open",
    }


def persist_market(market: Dict[str, Any]) -> None:
    ensure_evidence_dir()
    data = []
    if GENERATED.exists():
        try:
            data = json.loads(GENERATED.read_text(encoding="utf-8"))
        except json.JSONDecodeError:
            data = []
    data.append(market)
    GENERATED.parent.mkdir(parents=True, exist_ok=True)
    GENERATED.write_text(
        json.dumps(data, indent=2, ensure_ascii=False), encoding="utf-8"
    )


def main(argv: Any = None) -> int:
    argv = argv or sys.argv
    if len(argv) < 3:
        print(
            "usage: create_market_from_template.py <TEMPLATE_ID> <MARKET_NAME>",
            file=sys.stderr,
        )
        return 1
    tpl_id, name = argv[1], argv[2]
    policy = load_policy()
    if not policy.template_creation_enabled:
        print("feature flag mbp.create.by_template disabled", file=sys.stderr)
        return 3
    catalog = load_catalog()
    tpl = catalog.get_template(tpl_id)
    catalog.ensure_valid(tpl)
    validate_name(name)
    market = create_market(tpl, name)
    persist_market(market)
    span = TELEMETRY.emit(
        "market_created_template",
        {
            "template_id": tpl.id,
            "market_id": market["market_id"],
            "category": tpl.category,
        },
    )
    AUDIT_LOG.append(
        {
            "event": "market_created_template",
            "trace_id": span["trace_id"],
            "market": market,
        }
    )
    print(market["market_id"])
    return 0


if __name__ == "__main__":
    sys.exit(main())
