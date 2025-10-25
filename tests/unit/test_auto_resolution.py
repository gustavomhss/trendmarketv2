import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from services.auto_resolution import (  # noqa: E402
    AutoResolutionService,
    DecisionRule,
    IdempotencyKeyConflict,
    ManualOverride,
    QuorumEvaluation,
    TruthSourcePayload,
)


def make_service(tmp_path: Path) -> AutoResolutionService:
    audit_path = tmp_path / "audit" / "resolve.log"
    return AutoResolutionService(audit_log=audit_path)


def test_truth_source_final_preferred(tmp_path: Path) -> None:
    service = make_service(tmp_path)
    truth = TruthSourcePayload(
        source="registry",
        status="final",
        verdict="yes",
        confidence=0.98,
    )
    quorum = QuorumEvaluation(quorum_ok=True, suggested_outcome="yes", confidence=0.8)

    decision = service.apply_resolution(
        decision_id="dec-1",
        truth_payload=truth,
        quorum_result=quorum,
        actor="alice",
        role="resolver",
        idempotency_key="idem-1",
    )

    assert decision.outcome == "yes"
    assert decision.rule == DecisionRule.TRUTH_SOURCE_FINAL

    entries = service.load_audit_entries()
    assert len(entries) == 1
    assert entries[0]["outcome"] == "yes"
    assert entries[0]["truth_verdict"] == "yes"


def test_truth_source_override_on_conflict(tmp_path: Path) -> None:
    service = make_service(tmp_path)
    truth = TruthSourcePayload(
        source="registry",
        status="final",
        verdict="no",
        confidence=0.92,
    )
    quorum = QuorumEvaluation(quorum_ok=True, suggested_outcome="yes", confidence=0.7)

    decision = service.apply_resolution(
        decision_id="dec-2",
        truth_payload=truth,
        quorum_result=quorum,
        actor="alice",
        role="resolver",
        idempotency_key="idem-2",
    )

    assert decision.outcome == "no"
    assert decision.rule == DecisionRule.TRUTH_SOURCE_OVERRIDE


def test_quorum_consensus_when_truth_pending(tmp_path: Path) -> None:
    service = make_service(tmp_path)
    truth = TruthSourcePayload(
        source="registry",
        status="pending",
        verdict=None,
        confidence=0.2,
    )
    quorum = QuorumEvaluation(quorum_ok=True, suggested_outcome="yes", confidence=0.65)

    decision = service.apply_resolution(
        decision_id="dec-3",
        truth_payload=truth,
        quorum_result=quorum,
        actor="alice",
        role="resolver",
        idempotency_key="idem-3",
    )

    assert decision.outcome == "yes"
    assert decision.rule == DecisionRule.QUORUM_CONSENSUS


def test_manual_override_supersedes_all(tmp_path: Path) -> None:
    service = make_service(tmp_path)
    truth = TruthSourcePayload(
        source="registry",
        status="pending",
        verdict=None,
        confidence=0.3,
    )
    quorum = QuorumEvaluation(quorum_ok=False, suggested_outcome=None)

    decision = service.apply_resolution(
        decision_id="dec-4",
        truth_payload=truth,
        quorum_result=quorum,
        actor="bob",
        role="admin",
        idempotency_key="idem-4",
        manual_override=ManualOverride(outcome="refund", reason="operator override"),
    )

    assert decision.outcome == "refund"
    assert decision.rule == DecisionRule.MANUAL_OVERRIDE


def test_idempotency_replay_returns_same_result(tmp_path: Path) -> None:
    service = make_service(tmp_path)
    truth = TruthSourcePayload(
        source="registry",
        status="final",
        verdict="yes",
        confidence=0.99,
    )
    quorum = QuorumEvaluation(quorum_ok=True, suggested_outcome="yes", confidence=0.9)

    first = service.apply_resolution(
        decision_id="dec-5",
        truth_payload=truth,
        quorum_result=quorum,
        actor="carol",
        role="resolver",
        idempotency_key="shared",
    )
    second = service.apply_resolution(
        decision_id="dec-5",
        truth_payload=truth,
        quorum_result=quorum,
        actor="carol",
        role="resolver",
        idempotency_key="shared",
    )

    assert first.outcome == second.outcome
    assert first.trace_id == second.trace_id
    entries = service.load_audit_entries()
    assert len(entries) == 1


def test_idempotency_conflict_raises(tmp_path: Path) -> None:
    service = make_service(tmp_path)
    truth_a = TruthSourcePayload(
        source="registry",
        status="final",
        verdict="yes",
        confidence=0.7,
    )
    truth_b = TruthSourcePayload(
        source="registry",
        status="final",
        verdict="no",
        confidence=0.7,
    )
    quorum = QuorumEvaluation(quorum_ok=True, suggested_outcome="yes")

    service.apply_resolution(
        decision_id="dec-6",
        truth_payload=truth_a,
        quorum_result=quorum,
        actor="alice",
        role="resolver",
        idempotency_key="idem-x",
    )

    with pytest.raises(IdempotencyKeyConflict):
        service.apply_resolution(
            decision_id="dec-6",
            truth_payload=truth_b,
            quorum_result=quorum,
            actor="alice",
            role="resolver",
            idempotency_key="idem-x",
        )


def test_unauthorized_role_rejected(tmp_path: Path) -> None:
    service = make_service(tmp_path)
    truth = TruthSourcePayload(
        source="registry",
        status="final",
        verdict="yes",
        confidence=0.9,
    )
    quorum = QuorumEvaluation(quorum_ok=True, suggested_outcome="yes")

    with pytest.raises(PermissionError):
        service.apply_resolution(
            decision_id="dec-7",
            truth_payload=truth,
            quorum_result=quorum,
            actor="mallory",
            role="viewer",
            idempotency_key="idem-viewer",
        )
