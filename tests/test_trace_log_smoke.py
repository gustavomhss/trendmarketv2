import importlib.util
import json
import tempfile
import unittest
from pathlib import Path


SCRIPTS_DIR = Path(__file__).resolve().parents[1] / "scripts"
SCRIPT_PATH = SCRIPTS_DIR / "obs_trace_log_smoke.py"


def _load_module():
    spec = importlib.util.spec_from_file_location("obs_trace_log_smoke", SCRIPT_PATH)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)  # type: ignore[misc]
    return module


class TraceLogSmokeScriptTests(unittest.TestCase):
    def setUp(self) -> None:
        self.module = _load_module()

    def test_generate_trace_log_smoke_full_mode(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            state_path = Path(tmp) / "state.json"
            output_path = Path(tmp) / "trace.json"

            state_payload = {
                "meta": {"observability_level": "full"},
                "spans": [
                    {
                        "trace_id": "abc",
                        "span_id": "123",
                        "op": "swap",
                        "latency_seconds": 0.012,
                    }
                ],
                "logs": [
                    {
                        "trace_id": "abc",
                        "span_id": "123",
                        "message": "swap ok",
                        "level": "INFO",
                    }
                ],
            }
            state_path.write_text(json.dumps(state_payload), encoding="utf-8")

            payload = self.module.generate_trace_log_smoke(state_path, output_path)

            self.assertTrue(output_path.exists())
            written = json.loads(output_path.read_text(encoding="utf-8"))
            self.assertEqual(payload, written)
            self.assertFalse(payload["skipped"])
            self.assertEqual(payload["correlated_ratio"], 1.0)
            self.assertIn("sample", payload)

    def test_generate_trace_log_smoke_skips_for_min_mode(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            state_path = Path(tmp) / "state.json"
            output_path = Path(tmp) / "trace.json"

            state_payload = {
                "meta": {"observability_level": "min"},
                "spans": [],
                "logs": [],
            }
            state_path.write_text(json.dumps(state_payload), encoding="utf-8")

            payload = self.module.generate_trace_log_smoke(state_path, output_path)

            self.assertTrue(payload["skipped"])
            self.assertIsNone(payload["correlated_ratio"])
            self.assertTrue(output_path.exists())

    def test_generate_trace_log_smoke_requires_logs_for_full_mode(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            state_path = Path(tmp) / "state.json"
            output_path = Path(tmp) / "trace.json"

            state_payload = {
                "meta": {"observability_level": "full"},
                "spans": [
                    {
                        "trace_id": "abc",
                        "span_id": "123",
                        "op": "swap",
                        "latency_seconds": 0.012,
                    }
                ],
                "logs": [],
            }
            state_path.write_text(json.dumps(state_payload), encoding="utf-8")

            with self.assertRaises(RuntimeError) as ctx:
                self.module.generate_trace_log_smoke(state_path, output_path)

            self.assertEqual(str(ctx.exception), "TRACE_LOG_CORRELATION_FAIL")


if __name__ == "__main__":
    unittest.main()
