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
    ResolutionError,
    TruthSourceSignal,
)


def _service(tmp_path: Path) -> AutoResolutionService:
    audit_path = tmp_path / "audit" / "auto_resolve.log"
    return AutoResolutionService(audit_log=audit_path)


def test_quorum_resolution_success(tmp_path: Path) -> None:
    service = _service(tmp_path)
    record = service.apply(
        event_id="evt-1",
        quorum_votes=["accepted", "accepted", "rejected"],
        actor="alice",
        role=sorted(ALLOWED_AUTO_ROLES)[0],
        idempotency_key="idem-123456",
    )
    assert record.outcome == "accepted"
    assert record.truth_source_used is False
    assert record.quorum_ok is True

    audit_entries = service.load_audit_entries()
    assert len(audit_entries) == 1
    assert audit_entries[0]["action"] == "auto_resolve.apply"

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
        confidence=0.9,
        observed_at="2024-05-01T00:00:00Z",
    )

    record = service.apply(
        event_id="evt-2",
        quorum_votes=["accepted", "accepted", "accepted"],
        actor="bob",
        role="resolver",
        idempotency_key="idem-654321",
        truth_source=truth,
    )
    assert record.outcome == "rejected"
    assert record.truth_source_used is True
    assert record.quorum_ok is True

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
            quorum_votes=["accepted", "rejected"],
            actor="carol",
            role="resolver",
            idempotency_key="idem-abcdef",
        )


def test_manual_override_requires_role(tmp_path: Path) -> None:
    service = _service(tmp_path)

    with pytest.raises(PermissionError):
        service.apply(
            event_id="evt-4",
            quorum_votes=["rejected", "rejected", "accepted"],
            actor="mallory",
            role="resolver",
            idempotency_key="idem-override",
            manual_override="accepted",
        )

    # Valid manual override by a privileged role
    privileged_role = sorted(ALLOWED_MANUAL_ROLES)[0]
    record = service.apply(
        event_id="evt-4",
        quorum_votes=["rejected", "rejected", "accepted"],
        actor="dave",
        role=privileged_role,
        idempotency_key="idem-override2",
        manual_override="accepted",
        manual_reason="committee decision",
    )
    assert record.outcome == "accepted"
    assert record.manual_override is True
    assert record.truth_source_used is False

    events = service.load_decision_events()
    assert len(events) == 1
    assert events[0]["manual_override"] is True
    assert events[0]["rule"] == "manual.override"


def test_idempotency_returns_same_record(tmp_path: Path) -> None:
    service = _service(tmp_path)
    record = service.apply(
        event_id="evt-5",
        quorum_votes=["accepted", "accepted", "rejected"],
        actor="erin",
        role="resolver",
        idempotency_key="idem-unique",
    )

    repeat = service.apply(
        event_id="evt-5",
        quorum_votes=["rejected", "rejected", "rejected"],
        actor="erin",
        role="resolver",
        idempotency_key="idem-unique",
    )
    assert repeat is record

    with pytest.raises(ResolutionError):
        service.apply(
            event_id="evt-other",
            quorum_votes=["accepted", "accepted", "rejected"],
            actor="erin",
            role="resolver",
            idempotency_key="idem-unique",
        )

    events = service.load_decision_events()
    assert len(events) == 1
