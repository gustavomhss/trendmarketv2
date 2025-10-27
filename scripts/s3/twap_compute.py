#!/usr/bin/env python3
"""TWAP computation with telemetry, confidence intervals and events."""

from __future__ import annotations

import csv
import json
import math
import statistics
import sys
from datetime import datetime, timedelta, timezone
from pathlib import Path
from typing import Dict, List, Tuple

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from _telemetry import TelemetryEmitter, ensure_evidence_dir  # noqa: E402


def parse_ts(raw: str) -> datetime:
    raw = raw.replace("Z", "+00:00")
    dt = datetime.fromisoformat(raw)
    return dt.astimezone(timezone.utc)


def window_points(
    points: List[Tuple[datetime, float]], now: datetime, minutes: int
) -> List[float]:
    start = now - timedelta(minutes=minutes)
    return [p[1] for p in points if start <= p[0] <= now]


def window_avg(
    points: List[Tuple[datetime, float]], now: datetime, minutes: int
) -> float:
    values = window_points(points, now, minutes)
    return sum(values) / len(values) if values else float("nan")


def confidence_interval(values: List[float]) -> Dict[str, float]:
    if not values:
        return {"lower": math.nan, "upper": math.nan, "width": math.nan}
    if len(values) == 1:
        v = values[0]
        return {"lower": v, "upper": v, "width": 0.0}
    mean = sum(values) / len(values)
    stdev = statistics.pstdev(values)
    z = 2.576  # 99% confidence interval
    half = z * (stdev / math.sqrt(len(values))) if len(values) > 0 else 0.0
    return {"lower": mean - half, "upper": mean + half, "width": half * 2}


def main() -> int:
    if len(sys.argv) < 3:
        print("usage: twap_compute.py <PRICE_CSV> <OUT_CSV>", file=sys.stderr)
        return 1

    inp = Path(sys.argv[1])
    out = Path(sys.argv[2])
    evidence_dir = ensure_evidence_dir()
    events_path = evidence_dir / "twap_events.json"
    telemetry = TelemetryEmitter("twap_compute")

    rows: List[Tuple[datetime, float]] = []
    with inp.open() as f:
        reader = csv.DictReader(f)
        for row in reader:
            rows.append((parse_ts(row["ts"]), float(row["price"])))
    rows.sort(key=lambda x: x[0])

    out.parent.mkdir(parents=True, exist_ok=True)
    events: List[Dict[str, object]] = []
    with out.open("w", encoding="utf-8", newline="") as f:
        writer = csv.writer(f)
        writer.writerow(
            ["ts", "price", "twap_1m", "twap_5m", "twap_15m", "divergence_pct"]
        )
        for idx, (ts, price) in enumerate(rows):
            history = rows[: idx + 1]
            tw1 = window_avg(history, ts, 1)
            tw5 = window_avg(history, ts, 5)
            tw15 = window_avg(history, ts, 15)
            div = (
                abs(price - tw5) / tw5 * 100
                if (not math.isnan(tw5) and tw5 != 0)
                else float("nan")
            )
            writer.writerow(
                [
                    ts.isoformat(),
                    price,
                    round(tw1, 8) if not math.isnan(tw1) else "",
                    round(tw5, 8) if not math.isnan(tw5) else "",
                    round(tw15, 8) if not math.isnan(tw15) else "",
                    round(div, 4) if not math.isnan(div) else "",
                ]
            )
            window_values = window_points(history, ts, 5)
            ci = confidence_interval(window_values)
            ic_exceeded = False
            if not math.isnan(ci["lower"]) and not math.isnan(ci["upper"]):
                ic_exceeded = price < ci["lower"] or price > ci["upper"]
            span = telemetry.emit(
                "twap.compute",
                {
                    "ts": ts.isoformat(),
                    "price": price,
                    "twap_5m": tw5,
                    "divergence_pct": div,
                    "ic99_exceeded": ic_exceeded,
                },
            )
            events.append(
                {
                    "event": "twap_recomputed",
                    "ts": ts.isoformat(),
                    "price": price,
                    "twap": {
                        "m1": tw1,
                        "m5": tw5,
                        "m15": tw15,
                    },
                    "divergence_pct": div,
                    "ci99": ci,
                    "ic99_exceeded": ic_exceeded,
                    "trace_id": span["trace_id"],
                }
            )

    events_path.write_text(
        json.dumps(events, indent=2, ensure_ascii=False), encoding="utf-8"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
