from __future__ import annotations

import json
import sys
from pathlib import Path

import jsonschema
import pytest

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from services.auto_resolution import (  # noqa: E402
    AutoResolutionService,
    TruthSourceSignal,
)

SCHEMA_PATH = ROOT / "schemas" / "resolve.decision.v1.json"


@pytest.fixture()
def resolve_decision_validator() -> jsonschema.Draft7Validator:
    schema = json.loads(SCHEMA_PATH.read_text(encoding="utf-8"))
    return jsonschema.Draft7Validator(schema, format_checker=jsonschema.FormatChecker())


@pytest.fixture()
def resolve_decision_event(tmp_path: Path) -> dict:
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
    return events[0]


def test_resolve_decision_event_conforms_to_schema(
    resolve_decision_event: dict, resolve_decision_validator: jsonschema.Draft7Validator
) -> None:
    resolve_decision_validator.validate(resolve_decision_event)

    assert resolve_decision_event["schema_version"] == 1
    assert resolve_decision_event["truth_source_used"] is True
    assert resolve_decision_event["rule"] == "truth_source.trusted_feed"


def test_resolve_decision_schema_version_const_enforced(
    resolve_decision_event: dict, resolve_decision_validator: jsonschema.Draft7Validator
) -> None:
    invalid_event = {**resolve_decision_event, "schema_version": resolve_decision_event["schema_version"] + 1}

    with pytest.raises(jsonschema.ValidationError):
        resolve_decision_validator.validate(invalid_event)
