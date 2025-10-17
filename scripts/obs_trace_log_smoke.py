#!/usr/bin/env python3
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
STATE_PATH = ROOT / "out" / "obs_gatecheck" / "evidence" / "amm_obs_state.json"
OUTPUT_PATH = ROOT / "out" / "obs_gatecheck" / "evidence" / "trace_log_smoke.json"

if not STATE_PATH.exists():
    sys.exit("amm_obs_state.json is missing; run T2 first")

state = json.loads(STATE_PATH.read_text(encoding="utf-8"))
level = state.get("meta", {}).get("observability_level", "full").lower()
if level != "full":
    payload = {
        "total_spans": len(state.get("spans", [])),
        "correlated_entries": [],
        "correlated_ratio": None,
        "observability_level": level,
        "skipped": True,
    }
    OUTPUT_PATH.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print("TRACE_LOG_SMOKE_OK")
    sys.exit(0)

spans = state.get("spans", [])
logs = state.get("logs", [])
log_index = {(entry["trace_id"], entry["span_id"]): entry for entry in logs}
correlated = []
for span in spans:
    key = (span["trace_id"], span["span_id"])
    log = log_index.get(key)
    if log:
        correlated.append(
            {
                "trace_id": span["trace_id"],
                "span_id": span["span_id"],
                "op": span["op"],
                "latency_seconds": span["latency_seconds"],
                "log_message": log["message"],
                "log_level": log["level"],
            }
        )

if not spans:
    sys.exit("no spans captured for smoke test")

if len(correlated) != len(spans):
    sys.exit("TRACE_LOG_CORRELATION_FAIL")

payload = {
    "total_spans": len(spans),
    "correlated_entries": correlated,
    "correlated_ratio": 1.0,
    "observability_level": "full",
    "skipped": False,
    "sample": correlated[0],
}
OUTPUT_PATH.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
print("TRACE_LOG_SMOKE_OK")
