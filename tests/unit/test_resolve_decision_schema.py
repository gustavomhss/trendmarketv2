import json
import re
import sys
from datetime import datetime
from pathlib import Path
from urllib.parse import urlparse

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from services.auto_resolution import (  # noqa: E402
    AutoResolutionService,
    TruthSourceSignal,
)


def _check_type(value, type_name: str) -> bool:
    if type_name == "object":
        return isinstance(value, dict)
    if type_name == "array":
        return isinstance(value, list)
    if type_name == "string":
        return isinstance(value, str)
    if type_name == "boolean":
        return isinstance(value, bool)
    if type_name == "number":
        return isinstance(value, (int, float)) and not isinstance(value, bool)
    if type_name == "null":
        return value is None
    return False


def _validate(instance, schema, root_schema) -> None:
    if "$ref" in schema:
        ref = schema["$ref"]
        if ref.startswith("#/$defs/"):
            key = ref.split("/", 2)[-1]
            _validate(instance, root_schema["$defs"][key], root_schema)
            return
        raise AssertionError(f"Unsupported $ref: {ref}")

    if "anyOf" in schema:
        for option in schema["anyOf"]:
            try:
                _validate(instance, option, root_schema)
                return
            except AssertionError:
                continue
        raise AssertionError(f"Value {instance!r} does not satisfy anyOf {schema['anyOf']}")

    expected_type = schema.get("type")
    if expected_type is not None:
        if isinstance(expected_type, list):
            if not any(_check_type(instance, t) for t in expected_type):
                raise AssertionError(f"Value {instance!r} does not match types {expected_type}")
        else:
            if not _check_type(instance, expected_type):
                raise AssertionError(f"Value {instance!r} does not match type {expected_type}")

    if "const" in schema and instance != schema["const"]:
        raise AssertionError(f"Value {instance!r} does not equal const {schema['const']}")

    if "enum" in schema and instance not in schema["enum"]:
        raise AssertionError(f"Value {instance!r} not in enum {schema['enum']}")

    if isinstance(instance, str):
        min_length = schema.get("minLength")
        if min_length is not None and len(instance) < min_length:
            raise AssertionError(f"String {instance!r} shorter than minLength {min_length}")
        pattern = schema.get("pattern")
        if pattern is not None and re.fullmatch(pattern, instance) is None:
            raise AssertionError(f"String {instance!r} does not match pattern {pattern}")
        fmt = schema.get("format")
        if fmt == "date-time":
            try:
                datetime.fromisoformat(instance.replace("Z", "+00:00"))
            except ValueError as exc:  # pragma: no cover - defensive
                raise AssertionError("Invalid date-time format") from exc
        elif fmt == "uri":
            parsed = urlparse(instance)
            if not (parsed.scheme and parsed.netloc):
                raise AssertionError(f"Invalid URI: {instance!r}")

    if isinstance(instance, (int, float)) and not isinstance(instance, bool):
        minimum = schema.get("minimum")
        if minimum is not None and instance < minimum:
            raise AssertionError(f"Number {instance} below minimum {minimum}")
        maximum = schema.get("maximum")
        if maximum is not None and instance > maximum:
            raise AssertionError(f"Number {instance} above maximum {maximum}")

    if isinstance(instance, dict):
        props = schema.get("properties", {})
        required = schema.get("required", [])
        for key in required:
            if key not in instance:
                raise AssertionError(f"Missing required property {key}")
        additional_allowed = schema.get("additionalProperties", True)
        for key, value in instance.items():
            if key in props:
                _validate(value, props[key], root_schema)
            elif additional_allowed is False:
                raise AssertionError(f"Unexpected property {key}")
        return

    if isinstance(instance, list) and "items" in schema:
        for item in instance:
            _validate(item, schema["items"], root_schema)


def validate_with_schema(instance, schema):
    _validate(instance, schema, schema)


def test_resolve_decision_event_conforms_to_schema(tmp_path: Path) -> None:
    audit_path = tmp_path / "audit" / "auto_resolve.log"
    service = AutoResolutionService(audit_log=audit_path)

    truth = TruthSourceSignal(
        source="Trusted Feed",
        verdict="rejected",
        confidence=0.85,
        observed_at="2024-05-02T00:00:00Z",
        evidence_uri="https://evidence.trend/events/evt-42.json",
    )

    service.apply(
        event_id="evt-schema-1",
        quorum_votes=["accepted", "rejected", "accepted"],
        actor="validator",
        role="resolver",
        idempotency_key="idem-schema-1",
        truth_source=truth,
        evidence_uri="s3://resolve/evidence/evt-schema-1.json",
    )

    events = service.load_decision_events()
    assert len(events) == 1

    schema_path = ROOT / "schemas" / "resolve.decision.v1.json"
    with schema_path.open("r", encoding="utf-8") as fh:
        schema = json.load(fh)

    validate_with_schema(events[0], schema)

    assert events[0]["schema_version"] == 1
    assert events[0]["truth_source_used"] is True
    assert events[0]["rule"] == "truth_source.trusted_feed"
