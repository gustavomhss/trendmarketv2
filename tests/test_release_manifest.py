import json
import tempfile
import unittest
from pathlib import Path

from amm_obs.release import (
    ReleaseManifestError,
    generate_release_manifest,
    write_release_manifest,
)


def _write_json(path: Path, payload: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload), encoding="utf-8")


def _create_base_layout(tmpdir: Path) -> None:
    evidence = tmpdir / "evidence"
    logs = tmpdir / "logs"
    evidence.mkdir(parents=True, exist_ok=True)
    logs.mkdir(parents=True, exist_ok=True)


class ReleaseManifestTests(unittest.TestCase):
    def test_generate_release_manifest_success(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            out_dir = Path(tmp)
            _create_base_layout(out_dir)

            _write_json(
                out_dir / "summary.json",
                {"acceptance": "OK", "gatecheck": "OK", "profile": "full"},
            )

            bundle = out_dir / "bundle.zip"
            bundle.write_bytes(b"bundle")
            (out_dir / "bundle.sha256.txt").write_text(
                "deadbeef bundle.zip\n", encoding="utf-8"
            )

            evidence = out_dir / "evidence"
            _write_json(
                evidence / "metrics_summary.json",
                {
                    "p95_swap_seconds": 0.041,
                    "synthetic_swap_ok_ratio": 1.0,
                },
            )
            _write_json(
                evidence / "costs_cardinality.json",
                {
                    "total_estimated_usd_month": 42.5,
                    "max_ratio": 0.62,
                    "max_ratio_metric": "amm_op_latency_seconds_bucket",
                },
            )
            _write_json(
                evidence / "synthetic_probe.json",
                {
                    "ok": 58,
                    "total": 58,
                    "ok_ratio": 1.0,
                },
            )
            _write_json(
                evidence / "trace_log_smoke.json",
                {
                    "total_spans": 12,
                    "correlated_ratio": 1.0,
                    "observability_level": "full",
                },
            )
            _write_json(
                evidence / "pii_probe.json", {"status": "OK", "cpf": False}
            )
            _write_json(evidence / "chaos_summary.json", {"status": "GREEN"})
            _write_json(evidence / "baseline_perf.json", {"qps": 125})
            _write_json(evidence / "golden_traces.json", {"spans": 4})
            _write_json(
                evidence / "watchers_simulation.json",
                {
                    "simulated": True,
                    "alerts_expected": [
                        {"alert": "OBS_P95_Swap_TooHigh", "reason": "SLO"}
                    ],
                },
            )

            manifest = generate_release_manifest(out_dir)

            self.assertEqual(manifest["bundle"]["sha256"], "deadbeef")
            self.assertTrue(manifest["evidence_checks"]["metrics_summary"])
            self.assertEqual(manifest["synthetic_probe"]["ok_ratio"], 1.0)
            self.assertEqual(manifest["watchers"]["alerts_count"], 1)
            self.assertEqual(
                manifest["drills"]["trace_log_smoke"]["observability_level"],
                "full",
            )

            manifest_path = write_release_manifest(out_dir)
            self.assertTrue(manifest_path.exists())
            loaded = json.loads(manifest_path.read_text(encoding="utf-8"))
            self.assertEqual(loaded["bundle"]["size_bytes"], len(b"bundle"))

    def test_generate_release_manifest_requires_summary(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            out_dir = Path(tmp)
            _create_base_layout(out_dir)
            with self.assertRaises(FileNotFoundError):
                generate_release_manifest(out_dir)

    def test_generate_release_manifest_rejects_failed_summary(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            out_dir = Path(tmp)
            _create_base_layout(out_dir)
            _write_json(
                out_dir / "summary.json", {"acceptance": "FAIL", "gatecheck": "OK"}
            )

            with self.assertRaises(ReleaseManifestError) as ctx:
                generate_release_manifest(out_dir)
            self.assertEqual(str(ctx.exception), "SUMMARY_FAIL")

    def test_generate_release_manifest_invalid_json(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            out_dir = Path(tmp)
            _create_base_layout(out_dir)
            _write_json(
                out_dir / "summary.json", {"acceptance": "OK", "gatecheck": "OK"}
            )
            evidence = out_dir / "evidence"
            evidence.mkdir(parents=True, exist_ok=True)
            (evidence / "metrics_summary.json").write_text("{invalid", encoding="utf-8")

            with self.assertRaises(ReleaseManifestError) as ctx:
                generate_release_manifest(out_dir)
            self.assertIn("JSON inválido", str(ctx.exception))


if __name__ == "__main__":
    unittest.main()
