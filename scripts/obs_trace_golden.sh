#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(cd "${SCRIPT_DIR}/.." && pwd)"
GOLDEN_DIR="$ROOT_DIR/ops/traces/goldens"
EVID_DIR="${EVID:-${EVI:-$ROOT_DIR/out/obs_gatecheck/evidence}}"
mkdir -p "$EVID_DIR"
OUTPUT_PATH="$EVID_DIR/golden_traces.json"

if [ ! -d "$GOLDEN_DIR" ]; then
  echo "Missing golden fixtures directory: $GOLDEN_DIR" >&2
  exit 2
fi

TEMPO_URL="${TEMPO_URL:-${JAEGER_BASE_URL:-http://127.0.0.1:3200}}"
TRACE_SOURCE_OVERRIDE="${TRACE_GOLDEN_SOURCE:-}" 
MISSING_CODE=23

set +e
python3 - "$TEMPO_URL" "$TRACE_SOURCE_OVERRIDE" "$GOLDEN_DIR" "$OUTPUT_PATH" "$MISSING_CODE" <<'PY'
from __future__ import annotations

import json
import math
import sys
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, Iterable, List, Optional, Tuple
from urllib import parse, request, error as urlerror


@dataclass(frozen=True)
class AttributeRequirement:
    key: str
    equals: Optional[Any] = None
    approx: Optional[float] = None
    tolerance: float = 1e-9
    aliases: Tuple[str, ...] = ()

    @staticmethod
    def from_dict(payload: Dict[str, Any]) -> "AttributeRequirement":
        key = payload.get("key")
        if not isinstance(key, str) or not key:
            raise ValueError("attribute definition requires non-empty 'key'")
        equals = payload.get("equals") if "equals" in payload else None
        approx = payload.get("approx") if "approx" in payload else None
        tolerance = float(payload.get("tolerance", 1e-9))
        aliases_field = payload.get("aliases", ())
        if isinstance(aliases_field, list):
            aliases = tuple(str(item) for item in aliases_field if isinstance(item, str) and item)
        elif isinstance(aliases_field, tuple):
            aliases = tuple(item for item in aliases_field if isinstance(item, str) and item)
        elif isinstance(aliases_field, str) and aliases_field:
            aliases = (aliases_field,)
        else:
            aliases = ()
        return AttributeRequirement(key=key, equals=equals, approx=approx, tolerance=tolerance, aliases=aliases)

    @property
    def candidate_keys(self) -> Tuple[str, ...]:
        return (self.key, *self.aliases)


@dataclass
class Fixture:
    fixture_id: str
    operation: str
    service: str
    lookback: str
    limit: int
    attributes: Tuple[AttributeRequirement, ...]

    @staticmethod
    def from_path(path: Path) -> "Fixture":
        payload = json.loads(path.read_text(encoding="utf-8"))
        if not isinstance(payload, dict):
            raise ValueError(f"Fixture {path} must contain a JSON object")
        fixture_id = str(payload.get("id")) if payload.get("id") else path.stem
        operation = str(payload.get("operation") or fixture_id)
        service = str(payload.get("service") or "trendmarket-amm")
        lookback = str(payload.get("lookback") or "1h")
        limit_raw = payload.get("limit", 20)
        try:
            limit = int(limit_raw)
        except Exception as exc:  # pylint: disable=broad-except
            raise ValueError(f"Fixture {path}: invalid limit {limit_raw!r}") from exc
        attr_payload = payload.get("attributes")
        if not isinstance(attr_payload, list) or not attr_payload:
            raise ValueError(f"Fixture {path} must define a non-empty 'attributes' list")
        attributes = tuple(AttributeRequirement.from_dict(item) for item in attr_payload)
        return Fixture(
            fixture_id=fixture_id,
            operation=operation,
            service=service,
            lookback=lookback,
            limit=limit,
            attributes=attributes,
        )


@dataclass
class SpanCandidate:
    trace_id: str
    span_id: str
    attributes: Dict[str, Any]


def _load_payload(source: str) -> Dict[str, Any]:
    path = Path(source)
    if not path.exists():
        raise FileNotFoundError(source)
    return json.loads(path.read_text(encoding="utf-8"))


def _http_get(url: str) -> Dict[str, Any]:
    req = request.Request(url, headers={"Accept": "application/json"})
    with request.urlopen(req, timeout=15) as resp:  # nosec: B310
        charset = resp.headers.get_content_charset() or "utf-8"
        data = resp.read().decode(charset)
        return json.loads(data)


def fetch_traces(
    base_url: str,
    fixture: Fixture,
    override: Optional[str],
) -> Tuple[str, Dict[str, Any]]:
    if override:
        parsed = parse.urlparse(override)
        if parsed.scheme in {"", "file"}:
            path = Path(parsed.path or override)
            payload = _load_payload(path)
            return f"file://{path}", payload
        payload = json.loads(override)
        return "inline-json", payload
    query = parse.urlencode(
        {
            "service": fixture.service,
            "operation": fixture.operation,
            "lookback": fixture.lookback,
            "limit": str(fixture.limit),
        }
    )
    url = f"{base_url.rstrip('/')}/api/traces?{query}"
    payload = _http_get(url)
    return url, payload


def _normalize_value(value: Any) -> Any:
    if isinstance(value, dict) and {"value"}.issubset(value.keys()):
        return value.get("value")
    return value


def _extract_attributes(tag_list: Iterable[Dict[str, Any]]) -> Dict[str, Any]:
    attributes: Dict[str, Any] = {}
    for tag in tag_list or []:
        if not isinstance(tag, dict):
            continue
        key = tag.get("key")
        if not isinstance(key, str) or not key:
            continue
        value = _normalize_value(tag.get("value"))
        attributes[key] = value
    return attributes


def _floatify(value: Any) -> Optional[float]:
    if isinstance(value, bool):
        return float(value)
    if isinstance(value, (int, float)):
        return float(value)
    if isinstance(value, str):
        try:
            return float(value)
        except ValueError:
            return None
    return None


def build_span_candidates(payload: Dict[str, Any]) -> List[SpanCandidate]:
    spans: List[SpanCandidate] = []
    data = payload.get("data")
    if not isinstance(data, list):
        return spans
    for trace in data:
        if not isinstance(trace, dict):
            continue
        processes = trace.get("processes") if isinstance(trace.get("processes"), dict) else {}
        for span in trace.get("spans", []):
            if not isinstance(span, dict):
                continue
            attributes = _extract_attributes(span.get("tags", []))
            process_id = span.get("processID")
            if isinstance(process_id, str) and process_id in processes:
                process = processes[process_id]
                if isinstance(process, dict):
                    service_name = process.get("serviceName")
                    if isinstance(service_name, str) and "service.name" not in attributes:
                        attributes["service.name"] = service_name
                    proc_tags = process.get("tags", [])
                    proc_attrs = _extract_attributes(proc_tags)
                    for key, value in proc_attrs.items():
                        attributes.setdefault(key, value)
            spans.append(
                SpanCandidate(
                    trace_id=str(trace.get("traceID", "")),
                    span_id=str(span.get("spanID", "")),
                    attributes=attributes,
                )
            )
    return spans


def check_attribute(requirement: AttributeRequirement, attrs: Dict[str, Any]) -> Optional[str]:
    for key in requirement.candidate_keys:
        if key in attrs:
            value = attrs[key]
            if requirement.equals is not None:
                expected = requirement.equals
                if isinstance(expected, (int, float)) and isinstance(value, (int, float)):
                    if float(value) != float(expected):
                        return f"{key}={value!r} (expected {expected!r})"
                else:
                    if str(value) != str(expected):
                        return f"{key}={value!r} (expected {expected!r})"
            if requirement.approx is not None:
                numeric = _floatify(value)
                if numeric is None or math.isnan(numeric):
                    return f"{key} not numeric (expected ≈{requirement.approx})"
                if math.isinf(numeric):
                    return f"{key} infinite (expected ≈{requirement.approx})"
                if abs(numeric - float(requirement.approx)) > requirement.tolerance:
                    return f"{key}={numeric} (expected ≈{requirement.approx}±{requirement.tolerance})"
            return None
    return f"{requirement.key} missing"


def evaluate_fixture(
    fixture: Fixture,
    spans: List[SpanCandidate],
) -> Tuple[str, Dict[str, Any]]:
    if not spans:
        details = {
            "status": "missing_attributes",
            "ok": False,
            "missing": ["no spans returned"],
            "checked_spans": 0,
        }
        return fixture.fixture_id, details

    best_failure: Optional[Tuple[SpanCandidate, List[str]]] = None
    for span in spans:
        failures: List[str] = []
        for requirement in fixture.attributes:
            message = check_attribute(requirement, span.attributes)
            if message:
                failures.append(message)
        if not failures:
            details = {
                "status": "pass",
                "ok": True,
                "checked_spans": len(spans),
                "trace_id": span.trace_id,
                "span_id": span.span_id,
            }
            return fixture.fixture_id, details
        if best_failure is None or len(failures) < len(best_failure[1]):
            best_failure = (span, failures)

    assert best_failure is not None  # for mypy
    _, failures = best_failure
    details = {
        "status": "missing_attributes",
        "ok": False,
        "missing": failures,
        "checked_spans": len(spans),
    }
    return fixture.fixture_id, details


def main(argv: List[str]) -> int:
    if len(argv) != 5:
        raise SystemExit("Usage: <tempo_url> <override> <golden_dir> <output> <missing_code>")
    tempo_url, override, golden_dir_raw, output_raw, missing_code_raw = argv
    missing_code = int(missing_code_raw)

    golden_dir = Path(golden_dir_raw)
    if not golden_dir.exists():
        raise SystemExit(f"Golden fixtures directory not found: {golden_dir}")

    fixtures = []
    for path in sorted(golden_dir.glob("*.json")):
        fixtures.append(Fixture.from_path(path))
    if not fixtures:
        raise SystemExit(f"No fixtures found in {golden_dir}")

    results: Dict[str, Any] = {}
    failure_code: Optional[int] = None

    for fixture in fixtures:
        try:
            source_url, payload = fetch_traces(tempo_url, fixture, override or None)
        except FileNotFoundError as exc:
            results[fixture.fixture_id] = {
                "status": "error",
                "ok": False,
                "errors": [f"fixture source not found: {exc}"],
            }
            failure_code = failure_code or 2
            continue
        except (json.JSONDecodeError, urlerror.URLError, urlerror.HTTPError) as exc:
            results[fixture.fixture_id] = {
                "status": "error",
                "ok": False,
                "errors": [f"tempo query failed: {exc}"],
            }
            failure_code = failure_code or 2
            continue

        spans = build_span_candidates(payload)
        fixture_id, details = evaluate_fixture(fixture, spans)
        details["query"] = {
            "service": fixture.service,
            "operation": fixture.operation,
            "lookback": fixture.lookback,
            "limit": fixture.limit,
            "source": source_url,
        }
        results[fixture_id] = details
        if details.get("status") == "missing_attributes":
            failure_code = missing_code

    results["_meta"] = {
        "generated_at": datetime.now(timezone.utc).isoformat().replace("+00:00", "Z"),
        "tempo_url": tempo_url,
        "override": override or None,
    }

    output_path = Path(output_raw)
    output_path.write_text(json.dumps(results, indent=2, sort_keys=True), encoding="utf-8")

    if failure_code:
        return failure_code
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
PY
status=$?
set -e
if [ "$status" -eq 0 ]; then
  echo TRACE_GOLDEN_OK
elif [ "$status" -eq "$MISSING_CODE" ]; then
  echo TRACE_GOLDEN_FAIL
else
  exit "$status"
fi
exit "$status"
