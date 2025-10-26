#!/usr/bin/env bash
set -euo pipefail
IFS=$'\n\t'

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
OUT="$ROOT/out/obs_gatecheck"
EVI="$OUT/evidence"
mkdir -p "$EVI"

TRACE_GOLDEN_ROOT="$ROOT" TRACE_GOLDEN_EVIDENCE="$EVI" python3 - <<'PY'
import json
import os
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, Optional
from urllib import error, parse, request

ROOT = Path(os.environ["TRACE_GOLDEN_ROOT"])
EVIDENCE_DIR = Path(os.environ["TRACE_GOLDEN_EVIDENCE"])
FIXTURE_DIR = ROOT / "ops" / "traces" / "goldens"
TEMPO_BASE = os.environ.get("TEMPO_BASE", "http://127.0.0.1:3200").rstrip("/")
DEFAULT_SERVICE = os.environ.get("TRACE_SERVICE", "trendmarket-amm")
LOOKBACK = os.environ.get("TRACE_LOOKBACK", "1h")
DEFAULT_LIMIT = int(os.environ.get("TRACE_LIMIT", "20"))

report: Dict[str, Any] = {
    "generated_at": datetime.now(timezone.utc).isoformat().replace("+00:00", "Z"),
    "operations": {},
}
overall_ok = True


def load_fixture(path: Path) -> Dict[str, Any]:
    try:
        with path.open("r", encoding="utf-8") as handle:
            return json.load(handle)
    except json.JSONDecodeError as exc:
        raise ValueError(f"invalid JSON in fixture {path}: {exc}") from exc


def fetch_traces(operation: str, service: str, limit: int) -> Dict[str, Any]:
    params = parse.urlencode(
        {
            "service": service,
            "operation": operation,
            "limit": limit,
            "lookback": LOOKBACK,
        }
    )
    url = f"{TEMPO_BASE}/api/traces?{params}"
    req = request.Request(url, headers={"Accept": "application/json"})
    with request.urlopen(req, timeout=20) as response:
        return json.load(response)


def flatten_tags(span: Dict[str, Any]) -> Dict[str, Any]:
    tags: Dict[str, Any] = {}
    for tag in span.get("tags", []) or []:
        key = tag.get("key")
        if not key:
            continue
        tags[key] = tag.get("value")
    return tags


def to_float(value: Any) -> Optional[float]:
    if isinstance(value, (int, float)):
        return float(value)
    if isinstance(value, str):
        try:
            return float(value)
        except ValueError:
            return None
    return None


for fixture_path in sorted(FIXTURE_DIR.glob("*.json")):
    try:
        spec = load_fixture(fixture_path)
    except ValueError as exc:
        report["operations"][fixture_path.stem] = {"pass": False, "message": str(exc)}
        overall_ok = False
        continue

    operation = spec.get("operation")
    if not operation:
        report["operations"][fixture_path.stem] = {"pass": False, "message": "missing operation field"}
        overall_ok = False
        continue

    service = spec.get("service", DEFAULT_SERVICE)
    span_name = spec.get("span_name", operation)
    required_tags: Dict[str, Any] = spec.get("required_tags", {})
    min_traces = int(spec.get("min_traces", 1))
    limit = int(spec.get("limit", DEFAULT_LIMIT))

    op_report: Dict[str, Any] = {"pass": False}
    try:
        payload = fetch_traces(operation, service, limit)
    except error.URLError as exc:
        op_report["message"] = f"tempo request failed: {exc}"
        report["operations"][operation] = op_report
        overall_ok = False
        continue

    traces = payload.get("data") or []
    if len(traces) < min_traces:
        op_report["message"] = f"expected at least {min_traces} traces, got {len(traces)}"
        report["operations"][operation] = op_report
        overall_ok = False
        continue

    matched: Optional[Dict[str, Any]] = None
    for trace in traces:
        processes = trace.get("processes") or {}
        for span in trace.get("spans", []) or []:
            if span.get("operationName") != span_name:
                continue
            process = processes.get(span.get("processID") or "")
            service_name = process.get("serviceName") if isinstance(process, dict) else None
            if service_name and service_name != service:
                continue

            tags = flatten_tags(span)
            mismatch: Optional[str] = None
            for key, expected in required_tags.items():
                actual = tags.get(key)
                if actual is None:
                    mismatch = f"missing tag {key}"
                    break

                if isinstance(expected, dict) and "value" in expected:
                    target = expected.get("value")
                    tolerance = expected.get("tolerance")
                    target_num = to_float(target)
                    actual_num = to_float(actual)
                    if target_num is not None and actual_num is not None:
                        delta = abs(actual_num - target_num)
                        tol = float(tolerance) if tolerance is not None else 1e-12
                        if delta > tol:
                            mismatch = f"tag {key} differs by {delta} (tolerance {tol})"
                            break
                    else:
                        if actual != target:
                            mismatch = f"tag {key} expected {target!r}, got {actual!r}"
                            break
                else:
                    if actual != expected:
                        mismatch = f"tag {key} expected {expected!r}, got {actual!r}"
                        break

            if mismatch:
                continue

            matched = {
                "pass": True,
                "trace_id": span.get("traceID") or trace.get("traceID"),
                "span_id": span.get("spanID"),
                "message": "all required tags matched",
            }
            break
        if matched:
            break

    if not matched:
        op_report["message"] = "no spans matched required attributes"
        report["operations"][operation] = op_report
        overall_ok = False
    else:
        report["operations"][operation] = matched

output_path = EVIDENCE_DIR / "golden_traces.json"
with output_path.open("w", encoding="utf-8") as handle:
    json.dump(report, handle, indent=2, sort_keys=True)

if not overall_ok:
    sys.stderr.write("TRACE_GOLDEN_FAIL\n")
    sys.exit(1)

print("TRACE_GOLDEN_OK")
PY
