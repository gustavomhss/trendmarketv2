#!/usr/bin/env python3
"""Generate correlation evidence between AMM spans and structured logs."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Dict, Iterable, List, Tuple


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_STATE_PATH = (
    ROOT / "out" / "obs_gatecheck" / "evidence" / "amm_obs_state.json"
)
DEFAULT_OUTPUT_PATH = (
    ROOT / "out" / "obs_gatecheck" / "evidence" / "trace_log_smoke.json"
)


def _build_log_index(entries: Iterable[Dict[str, object]]) -> Dict[Tuple[str, str], Dict[str, object]]:
    index: Dict[Tuple[str, str], Dict[str, object]] = {}
    for entry in entries:
        trace_id = str(entry.get("trace_id"))
        span_id = str(entry.get("span_id"))
        index[(trace_id, span_id)] = dict(entry)
    return index


def generate_trace_log_smoke(state_path: Path, output_path: Path) -> Dict[str, object]:
    """Create the trace/log correlation payload and persist it to ``output_path``."""

    if not state_path.exists():
        raise FileNotFoundError("amm_obs_state.json is missing; run T2 first")

    state = json.loads(state_path.read_text(encoding="utf-8"))
    level = state.get("meta", {}).get("observability_level", "full").lower()
    spans: List[Dict[str, object]] = list(state.get("spans", []))

    output_path.parent.mkdir(parents=True, exist_ok=True)

    if level != "full":
        payload = {
            "total_spans": len(spans),
            "correlated_entries": [],
            "correlated_ratio": None,
            "observability_level": level,
            "skipped": True,
        }
        output_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
        return payload

    logs: List[Dict[str, object]] = list(state.get("logs", []))
    if not spans:
        raise RuntimeError("no spans captured for smoke test")

    log_index = _build_log_index(logs)
    correlated = []
    for span in spans:
        key = (str(span.get("trace_id")), str(span.get("span_id")))
        log = log_index.get(key)
        if not log:
            raise RuntimeError("TRACE_LOG_CORRELATION_FAIL")
        correlated.append(
            {
                "trace_id": span.get("trace_id"),
                "span_id": span.get("span_id"),
                "op": span.get("op"),
                "latency_seconds": span.get("latency_seconds"),
                "log_message": log.get("message"),
                "log_level": log.get("level"),
            }
        )

    payload = {
        "total_spans": len(spans),
        "correlated_entries": correlated,
        "correlated_ratio": 1.0,
        "observability_level": "full",
        "skipped": False,
        "sample": correlated[0],
    }
    output_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    return payload


def parse_args(argv: Iterable[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--state",
        type=Path,
        default=DEFAULT_STATE_PATH,
        help="Path to amm_obs_state.json (default: out/obs_gatecheck/evidence).",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=DEFAULT_OUTPUT_PATH,
        help="Where to write trace_log_smoke.json (default: out/obs_gatecheck/evidence).",
    )
    return parser.parse_args(list(argv) if argv is not None else None)


def main(argv: Iterable[str] | None = None) -> int:
    args = parse_args(argv)

    try:
        generate_trace_log_smoke(args.state, args.output)
    except FileNotFoundError as exc:
        sys.exit(str(exc))
    except RuntimeError as exc:
        sys.exit(str(exc))

    print("TRACE_LOG_SMOKE_OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
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
