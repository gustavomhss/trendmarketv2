import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from services.auto_resolution import (  # noqa: E402
    AutoResolutionAPI,
    AutoResolutionService,
    DecisionRule,
    IdempotencyKeyConflict,
)


def make_api(tmp_path: Path) -> AutoResolutionAPI:
    audit_path = tmp_path / "audit" / "resolve.log"
    service = AutoResolutionService(audit_log=audit_path)
    return AutoResolutionAPI(service), service


def test_api_apply_success_flow(tmp_path: Path) -> None:
    api, service = make_api(tmp_path)
    payload = {
        "schema_version": 1,
        "decision_id": "case-1",
        "truth_source": "registry",
        "quorum": True,
        "payload": {
            "truth": {"status": "final", "verdict": "yes", "confidence": 0.97},
            "quorum": {"outcome": "yes", "confidence": 0.82, "contributors": ["alpha", "beta"]},
            "market_id": "PM:ABC",
        },
    }

    response = api.resolve_apply(payload, actor="alice", role="resolver", idempotency_key="k-1")

    assert response["outcome"] == "yes"
    assert response["rule"] == DecisionRule.TRUTH_SOURCE_FINAL

    entries = service.load_audit_entries()
    assert len(entries) == 1
    assert entries[0]["metadata"]["market_id"] == "PM:ABC"


def test_api_manual_override(tmp_path: Path) -> None:
    api, service = make_api(tmp_path)
    payload = {
        "schema_version": 1,
        "decision_id": "case-2",
        "truth_source": "registry",
        "quorum": False,
        "payload": {
            "truth": {"status": "pending", "confidence": 0.2},
            "quorum": {"outcome": None},
            "manual_override": {"outcome": "refund", "reason": "operator"},
        },
    }

    response = api.resolve_apply(payload, actor="carol", role="admin", idempotency_key="k-2")

    assert response["outcome"] == "refund"
    assert response["rule"] == DecisionRule.MANUAL_OVERRIDE

    entries = service.load_audit_entries()
    assert entries[0]["manual_override"] == "operator"


def test_api_idempotency_conflict(tmp_path: Path) -> None:
    api, _ = make_api(tmp_path)
    base = {
        "schema_version": 1,
        "decision_id": "case-3",
        "truth_source": "registry",
        "quorum": True,
        "payload": {
            "truth": {"status": "final", "verdict": "yes"},
            "quorum": {"outcome": "yes"},
        },
    }
    api.resolve_apply(base, actor="alice", role="resolver", idempotency_key="k-shared")

    modified = {
        **base,
        "payload": {
            "truth": {"status": "final", "verdict": "no"},
            "quorum": {"outcome": "no"},
        },
    }

    with pytest.raises(IdempotencyKeyConflict):
        api.resolve_apply(modified, actor="alice", role="resolver", idempotency_key="k-shared")


def test_api_enforces_rbac(tmp_path: Path) -> None:
    api, _ = make_api(tmp_path)
    payload = {
        "schema_version": 1,
        "decision_id": "case-4",
        "truth_source": "registry",
        "quorum": True,
        "payload": {
            "truth": {"status": "final", "verdict": "yes"},
            "quorum": {"outcome": "yes"},
        },
    }

    with pytest.raises(PermissionError):
        api.resolve_apply(payload, actor="mallory", role="viewer", idempotency_key="k-4")
from services.auto_resolution import AutoResolutionService, apply_resolution  # noqa: E402


def _service(tmp_path: Path) -> AutoResolutionService:
    audit_path = tmp_path / "audit" / "auto_resolve.log"
    return AutoResolutionService(audit_log=audit_path)


def test_apply_resolution_handler_idempotency(tmp_path: Path) -> None:
    service = _service(tmp_path)
    payload = {
        "event_id": "evt-api-1",
        "quorum_votes": ["accepted", "accepted", "rejected"],
        "actor": "zoe",
        "role": "resolver",
        "idempotency_key": "idem-api-1234",
    }

    first = apply_resolution(payload, service=service)
    assert first["outcome"] == "accepted"
    assert first["decision_id"]
    assert first["truth_source_used"] is False

    second = apply_resolution(payload, service=service)
    assert second == first

    entries = service.load_audit_entries()
    assert len(entries) == 1
    assert entries[0]["idempotency_key"] == "idem-api-1234"


def test_apply_resolution_manual_fallback(tmp_path: Path) -> None:
    service = _service(tmp_path)
    payload = {
        "event_id": "evt-api-2",
        "quorum_votes": ["accepted", "rejected"],
        "actor": "ivy",
        "role": "admin",
        "idempotency_key": "idem-api-5678",
        "manual_override": "rejected",
        "manual_reason": "insufficient quorum",
    }

    result = apply_resolution(payload, service=service)
    assert result["outcome"] == "rejected"
    assert result["manual_override"] is True
    assert result["truth_source_used"] is False


def test_apply_resolution_requires_fields(tmp_path: Path) -> None:
    service = _service(tmp_path)
    with pytest.raises(ValueError):
        apply_resolution({"event_id": "evt"}, service=service)
