import json
import unittest
from pathlib import Path

from amm_obs import AMMObservability


class AMMObservabilityTests(unittest.TestCase):
    def setUp(self) -> None:
        self.obs = AMMObservability(seed=123)
        self.obs.simulate_unit_load()

    def test_simulate_unit_load_populates_metrics(self) -> None:
        snapshot = self.obs.metrics_snapshot()
        operations = snapshot["operations"]
        # All core operations should have deterministic counts and histograms
        self.assertEqual(
            sorted(operations.keys()),
            ["add_liquidity", "cdc_consume", "pricing", "remove_liquidity", "swap"],
        )
        for op, payload in operations.items():
            with self.subTest(op=op):
                self.assertGreater(payload["count"], 0)
                # histograms include +Inf bucket
                self.assertIn("+Inf", payload["buckets"])

    def test_cardinality_breakdown_has_budgets(self) -> None:
        breakdown = self.obs.cardinality_breakdown()
        metrics = breakdown["metrics"]
        self.assertIn("amm_op_latency_seconds_bucket", metrics)
        for name in [
            "amm_op_latency_seconds_bucket",
            "data_freshness_seconds",
            "cdc_lag_seconds",
            "drift_score",
            "hook_executions_total",
            "synthetic_latency_seconds_bucket",
        ]:
            with self.subTest(metric=name):
                payload = metrics[name]
                self.assertIn("series", payload)
                self.assertIn("est_usd_month", payload)

    def test_export_prometheus_contains_synthetic_metrics(self) -> None:
        text = self.obs.export_prometheus()
        self.assertIn("# HELP synthetic_requests_total", text)
        self.assertIn("synthetic_ok_ratio", text)

    def test_serialization_round_trip(self) -> None:
        tmp = Path("tests/tmp_state.json")
        try:
            self.obs.write_state(tmp)
            data = json.loads(tmp.read_text(encoding="utf-8"))
            self.assertEqual(data["meta"]["observability_level"], "full")
            self.assertEqual(len(data["spans"]), len(self.obs.serialize()["spans"]))
        finally:
            if tmp.exists():
                tmp.unlink()


class ObservabilityLevelOffTests(unittest.TestCase):
    def test_metrics_disabled_when_off(self) -> None:
        obs = AMMObservability(observability_level="off")
        obs.simulate_unit_load()
        self.assertEqual(obs.export_prometheus().strip(), "# Observability disabled (level=off)")
        snapshot = obs.metrics_snapshot()
        self.assertEqual(snapshot["operations"], {})
        # Even in off mode synthetic probes record their latest runs so that
        # release evidence can report success ratios. Non-synthetic supporting
        # gauges must remain absent.
        supporting = snapshot["supporting"]
        self.assertEqual(list(supporting.keys()), ["synthetic"])


if __name__ == "__main__":
    unittest.main()
