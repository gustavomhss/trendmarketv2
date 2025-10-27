import argparse
import csv
import json
import os
from dataclasses import dataclass
from pathlib import Path
from statistics import mean
from typing import Dict, List
import random
import time

from services.oracles.aggregator import Quote, aggregate_quorum
from services.oracles.twap import TwapEngine
from services.telemetry import EventEmitter, TelemetryManager, TelemetrySettings

SCENARIOS = {"spike", "gap", "burst"}
REPORT_VERSION = 1
DEFAULT_SYMBOL = "BRLUSD"

_TELEMETRY = TelemetryManager(TelemetrySettings(service_name="simulation-harness"))
_RUN_COUNTER = _TELEMETRY.counter(
    "mbp_simulation_runs_total",
    "Total deterministic simulations executed.",
    labelnames=("scenario",),
)
_RUN_DURATION = _TELEMETRY.histogram(
    "mbp_simulation_run_duration_seconds",
    "Duration of simulation scenarios.",
    buckets=(0.01, 0.05, 0.1, 0.25, 0.5, 1.0, 2.0, 5.0),
    labelnames=("scenario",),
)


def _event_log() -> EventEmitter:
    return _TELEMETRY.event_log(
        "MBP_SIM_EVENT_LOG",
        Path("out/sim/events.jsonl"),
    )


@dataclass
class ScenarioStats:
    quorum_hits: int
    divergence_max: float
    staleness_max: int
    total_points: int

    def quorum_ratio(self) -> float:
        return self.quorum_hits / self.total_points if self.total_points else 0.0


def load_orders(csv_path: Path) -> List[Dict[str, float]]:
    with csv_path.open("r", encoding="utf-8") as fh:
        reader = csv.DictReader(fh)
        rows = []
        for row in reader:
            rows.append(
                {
                    "ts": float(row["ts"]),
                    "price": float(row["price"]),
                    "qty": float(row.get("qty", 0)),
                }
            )
        return rows


def simulate_scenario(
    fixtures: Path, scenario: str, out_path: Path, seed: int
) -> Dict[str, object]:
    rng = random.Random(seed)
    orders_file = fixtures / f"orders_{scenario}.csv"
    orders = load_orders(orders_file)
    depth_info = json.loads(
        (fixtures / "market_depth.json").read_text(encoding="utf-8")
    )

    engine = TwapEngine(symbol=DEFAULT_SYMBOL)
    quorum_hits = 0
    divergence_max = 0.0
    staleness_max = 0
    agg_prices: List[float] = []
    last_ts_ms = 0

    started = time.perf_counter()

    with _TELEMETRY.span(
        "sim.run",
        attributes={"sim.scenario": scenario, "sim.seed": seed},
    ):
        for idx, order in enumerate(orders):
            ts_ms = int(order["ts"] * 1000)
            last_ts_ms = ts_ms
            quotes = []
            base_price = order["price"]
            for offset, source in enumerate(["alpha", "beta", "gamma"]):
                adjustment = (offset - 1) * 0.0004 + rng.uniform(-0.0001, 0.0001)
                quote_price = base_price * (1 + adjustment)
                quote_ts = ts_ms - (offset * 5_000)
                quotes.append(
                    Quote(
                        symbol=DEFAULT_SYMBOL,
                        price=quote_price,
                        ts_ms=quote_ts,
                        source=source,
                    )
                )

            result = aggregate_quorum(DEFAULT_SYMBOL, quotes, now_ms=ts_ms)
            if result.quorum_ok:
                quorum_hits += 1
            if result.divergence_pct is not None:
                divergence_max = max(divergence_max, result.divergence_pct)
            if result.max_staleness_ms is not None:
                staleness_max = max(staleness_max, result.max_staleness_ms)
            if result.agg_price is not None:
                agg_prices.append(result.agg_price)

            if scenario == "gap" and idx > len(orders) // 2:
                pass
            else:
                engine.ingest("primary", base_price, ts_ms)

            engine.ingest("secondary", base_price * 1.0002, ts_ms)

            if scenario == "burst" and idx % 5 == 0:
                extra_ts = ts_ms + 200
                engine.ingest("secondary", base_price * 1.0004, extra_ts)

        twap_snapshot = engine.compute(now_ms=last_ts_ms + 1_000)

    duration = time.perf_counter() - started
    _RUN_COUNTER.labels(scenario=scenario).inc()
    _RUN_DURATION.labels(scenario=scenario).observe(duration)

    report = {
        "scenario": scenario,
        "symbol": DEFAULT_SYMBOL,
        "seed": seed,
        "report_version": REPORT_VERSION,
        "generated_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "orders": {
            "count": len(orders),
            "avg_price": mean(o["price"] for o in orders) if orders else 0.0,
            "max_price": max(o["price"] for o in orders) if orders else 0.0,
            "min_price": min(o["price"] for o in orders) if orders else 0.0,
            "total_qty": sum(o["qty"] for o in orders),
        },
        "market_depth": depth_info.get(DEFAULT_SYMBOL, {}),
        "oracle": {
            "quorum_ratio": round(
                ScenarioStats(
                    quorum_hits, divergence_max, staleness_max, len(orders)
                ).quorum_ratio(),
                4,
            ),
            "divergence_max": round(divergence_max, 6),
            "staleness_max_ms": staleness_max,
            "agg_price_avg": mean(agg_prices) if agg_prices else None,
        },
        "twap": {
            "source": twap_snapshot["source"],
            "twap": twap_snapshot["twap"],
            "staleness_ms": twap_snapshot["staleness_ms"],
            "failover_time_s": twap_snapshot["failover_time_s"],
            "events": [
                {
                    "ts_ms": event.ts_ms,
                    "kind": event.kind,
                    "details": event.details,
                }
                for event in engine.snapshot_events()
            ],
        },
        "duration_seconds": duration,
    }

    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    _event_log().emit(
        "sim.run",
        {
            "scenario": scenario,
            "seed": seed,
            "duration_seconds": duration,
            "report_path": str(out_path),
            "quorum_ratio": report["oracle"]["quorum_ratio"],
        },
    )
    return report


def main() -> None:
    parser = argparse.ArgumentParser(description="MBP deterministic simulation harness")
    parser.add_argument(
        "--fixtures", type=Path, required=True, help="Path to fixtures directory"
    )
    parser.add_argument("--scenario", choices=sorted(SCENARIOS), required=True)
    parser.add_argument(
        "--out", type=Path, required=True, help="Output path for the report JSON"
    )
    args = parser.parse_args()

    seed_env = int(os.environ.get("SEED", "42"))
    simulate_scenario(args.fixtures, args.scenario, args.out, seed_env)


if __name__ == "__main__":
    main()
