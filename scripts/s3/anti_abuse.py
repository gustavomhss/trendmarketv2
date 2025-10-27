#!/usr/bin/env python3
"""Anti-abuse detector for S3 gatecheck."""
from __future__ import annotations

import json
import os
import sys
from collections import defaultdict, deque
from dataclasses import dataclass
from pathlib import Path
from typing import Deque, Dict, Iterable, List, Tuple

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from _telemetry import TelemetryEmitter, ensure_evidence_dir  # noqa: E402
from _yaml import load as yaml_load  # noqa: E402

POLICY_PATH = Path(os.getenv("MBP_POLICY_FILE", "configs/policies/mbp_s3.yml"))
EVIDENCE_PATH = Path(os.getenv("MBP_ABUSE_FLAGS", "out/s3_gatecheck/abuse_flags.json"))
TELEMETRY = TelemetryEmitter("anti_abuse")


@dataclass
class RiskCaps:
    max_trade_rate_per_min: int
    max_exposure_per_user: float
    max_open_interest: float
    cooldown_s: int = 120


def load_caps() -> Dict[str, RiskCaps]:
    raw = yaml_load(POLICY_PATH) or {}
    caps: Dict[str, RiskCaps] = {}
    for key, cfg in (raw.get("risk_caps") or {}).items():
        if not key.startswith("template_"):
            continue
        category = "binary" if key.endswith("yesno") else "continuous"
        caps[category] = RiskCaps(
            max_trade_rate_per_min=int(cfg.get("max_trade_rate_per_min", 0)),
            max_exposure_per_user=float(cfg.get("max_exposure_per_user", 0)),
            max_open_interest=float(cfg.get("max_open_interest", 0)),
            cooldown_s=int(cfg.get("cooldown_s", 120)),
        )
    return caps


def detect_abuse(orders: Iterable[Dict[str, object]]) -> List[Dict[str, object]]:
    caps_by_category = load_caps()
    exposure: Dict[Tuple[str, str], float] = defaultdict(float)
    windows: Dict[Tuple[str, str], Deque[int]] = defaultdict(deque)
    cooldown_until: Dict[Tuple[str, str], int] = {}
    events: List[Dict[str, object]] = []

    for order in sorted(orders, key=lambda o: int(o.get("ts", 0))):
        user = str(order.get("user"))
        market = str(order.get("market_id"))
        category = str(order.get("template_category", ""))
        qty = float(order.get("qty", 0))
        ts = int(order.get("ts", 0))
        cap = caps_by_category.get(category)
        if not cap:
            continue
        key = (user, market)

        win = windows[key]
        win.append(ts)
        while win and ts - win[0] > 60:
            win.popleft()
        if cap.max_trade_rate_per_min and len(win) > cap.max_trade_rate_per_min:
            events.append(
                {
                    "event": "abuse_flagged",
                    "user": user,
                    "market_id": market,
                    "reason": "burst",
                    "severity": "medium",
                    "trace_id": TELEMETRY.emit(
                        "abuse.detect", {"user": user, "market_id": market, "reason": "burst"}
                    )["trace_id"],
                }
            )
            cooldown_until[key] = ts + cap.cooldown_s

        exposure[key] += abs(qty)
        if cap.max_exposure_per_user and exposure[key] > cap.max_exposure_per_user:
            events.append(
                {
                    "event": "abuse_flagged",
                    "user": user,
                    "market_id": market,
                    "reason": "exposure",
                    "severity": "high",
                    "trace_id": TELEMETRY.emit(
                        "abuse.detect", {"user": user, "market_id": market, "reason": "exposure"}
                    )["trace_id"],
                }
            )

        cooldown_deadline = cooldown_until.get(key)
        if cooldown_deadline and ts < cooldown_deadline:
            events.append(
                {
                    "event": "abuse_flagged",
                    "user": user,
                    "market_id": market,
                    "reason": "cooldown_violation",
                    "severity": "medium",
                    "trace_id": TELEMETRY.emit(
                        "abuse.detect", {"user": user, "market_id": market, "reason": "cooldown"}
                    )["trace_id"],
                }
            )
            cooldown_until[key] = ts + cap.cooldown_s

    return events


def main() -> int:
    if len(sys.argv) < 2:
        print("usage: anti_abuse.py <ORDERS_JSON>", file=sys.stderr)
        return 1
    orders_path = Path(sys.argv[1])
    orders = json.loads(orders_path.read_text(encoding="utf-8"))
    events = detect_abuse(orders)
    ensure_evidence_dir()
    EVIDENCE_PATH.parent.mkdir(parents=True, exist_ok=True)
    EVIDENCE_PATH.write_text(json.dumps(events, indent=2, ensure_ascii=False), encoding="utf-8")
    print(len(events))
    return 0


if __name__ == "__main__":
    sys.exit(main())
