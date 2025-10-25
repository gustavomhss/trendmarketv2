import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[3]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from services.auto_resolution.service import (  # noqa: E402
    ALLOWED_AUTO_ROLES,
    ALLOWED_MANUAL_ROLES,
    AutoResolutionService,
    ResolutionConflict,
    ResolutionError,
    TruthSourceSignal,
)


def _service(tmp_path: Path) -> AutoResolutionService:
    audit_path = tmp_path / "out" / "resolve" / "audit.log"
    metrics_path = tmp_path / "out" / "resolve" / "metrics.jsonl"
    return AutoResolutionService(audit_log=audit_path, metrics_log=metrics_path)


def _votes() -> dict:
    return {
        "votes": [
            {"source": "alpha", "verdict": "accepted", "weight": 1.0},
            {"source": "beta", "verdict": "accepted", "weight": 1.0},
            {"source": "gamma", "verdict": "rejected", "weight": 1.0},
        ],
        "divergence_pct": 0.004,
    }


def test_quorum_resolution_success(tmp_path: Path) -> None:
    service = _service(tmp_path)
    record = service.apply(
        event_id="evt-1",
        quorum_votes=_votes(),
        actor="alice",
        role="operator",
        idempotency_key="idem-123456",
        resource_version=0,
    )
    assert record.outcome == "accepted"
    assert record.truth_source_used is False
    assert record.quorum_ok is True
    assert record.resource_version == 1
    assert record.agreement_score == pytest.approx(0.6667, rel=1e-4)

    audit_entries = service.load_audit_entries()
    assert len(audit_entries) == 1
    assert audit_entries[0]["resource_version"] == 1

    metrics_entries = service.load_metrics_entries()
    assert metrics_entries[0]["span"] == "auto_resolve.eval"
    assert metrics_entries[0]["status"] == "success"

    events = service.load_decision_events()
    assert len(events) == 1
    assert events[0]["schema_version"] == 1
    assert events[0]["rule"] == "auto.quorum"
    assert events[0]["decision"] == "accepted"


def test_truth_source_override(tmp_path: Path) -> None:
    service = _service(tmp_path)
    truth = TruthSourceSignal(
        source="trusted_feed",
        verdict="rejected",
        confidence=0.92,
        observed_at="2024-05-01T00:00:00Z",
    )

    record = service.apply(
        event_id="evt-2",
        quorum_votes={
            "votes": [
                {"source": "alpha", "verdict": "accepted", "weight": 1.0},
                {"source": "beta", "verdict": "rejected", "weight": 1.0},
                {"source": "gamma", "verdict": "rejected", "weight": 1.0},
            ],
            "divergence_pct": 0.02,
        },
        actor="bob",
        role="operator",
        idempotency_key="idem-654321",
        truth_source=truth,
        resource_version=0,
    )
    assert record.outcome == "rejected"
    assert record.truth_source_used is True
    assert record.quorum_ok is False  # divergence exceeded threshold

    events = service.load_decision_events()
    assert len(events) == 1
    assert events[0]["truth_source_used"] is True
    assert events[0]["rule"] == "truth_source.trusted_feed"
    assert events[0]["truth_source"]["source"] == "trusted_feed"


def test_quorum_failure_requires_manual_or_truth_source(tmp_path: Path) -> None:
    service = _service(tmp_path)

    with pytest.raises(ResolutionError):
        service.apply(
            event_id="evt-3",
            quorum_votes={"votes": []},
            actor="carol",
            role="operator",
            idempotency_key="idem-abcdef",
            resource_version=0,
        )


def test_manual_override_requires_role_and_evidence(tmp_path: Path) -> None:
    service = _service(tmp_path)

    with pytest.raises(PermissionError):
        service.apply(
            event_id="evt-4",
            quorum_votes=_votes(),
            actor="mallory",
            role="operator",
            idempotency_key="idem-override",
            manual_override="accepted",
            resource_version=0,
        )

    privileged_role = sorted(ALLOWED_MANUAL_ROLES)[0]
    with pytest.raises(ValueError):
        service.apply(
            event_id="evt-4",
            quorum_votes=_votes(),
            actor="dave",
            role=privileged_role,
            idempotency_key="idem-override1",
            manual_override="accepted",
            manual_reason="committee decision",
            resource_version=0,
        )

    record = service.apply(
        event_id="evt-4",
        quorum_votes=_votes(),
        actor="dave",
        role=privileged_role,
        idempotency_key="idem-override2",
        manual_override="accepted",
        manual_reason="committee decision",
        evidence_uri="s3://bucket/proof",
        resource_version=0,
    )
    assert record.outcome == "accepted"
    assert record.manual_override is True
    assert record.truth_source_used is False

    events = service.load_decision_events()
    assert len(events) == 1
    assert events[0]["manual_override"] is True
    assert events[0]["rule"] == "manual.override"


def test_conflict_on_stale_resource_version(tmp_path: Path) -> None:
    service = _service(tmp_path)
    service.apply(
        event_id="evt-5",
        quorum_votes=_votes(),
        actor="erin",
        role="operator",
        idempotency_key="idem-unique",
        resource_version=0,
    )

    with pytest.raises(ResolutionConflict):
        service.apply(
            event_id="evt-5",
            quorum_votes=_votes(),
            actor="erin",
            role="operator",
            idempotency_key="idem-unique-2",
            resource_version=0,
        )


def test_idempotency_returns_same_record(tmp_path: Path) -> None:
    service = _service(tmp_path)
    record = service.apply(
        event_id="evt-6",
        quorum_votes=_votes(),
        actor="zoe",
        role="operator",
        idempotency_key="idem-unique",
        resource_version=0,
    )

    repeat = service.apply(
        event_id="evt-6",
        quorum_votes={
            "votes": [
                {"source": "alpha", "verdict": "rejected", "weight": 1.0},
                {"source": "beta", "verdict": "rejected", "weight": 1.0},
                {"source": "gamma", "verdict": "rejected", "weight": 1.0},
            ],
            "divergence_pct": 0.001,
        },
        actor="zoe",
        role="operator",
        idempotency_key="idem-unique",
        resource_version=0,
    )
    assert repeat is record

    with pytest.raises(ResolutionError):
        service.apply(
            event_id="evt-7",
            quorum_votes=_votes(),
            actor="zoe",
            role="operator",
            idempotency_key="idem-unique",
            resource_version=0,
        )

    events = service.load_decision_events()
    assert len(events) == 1
