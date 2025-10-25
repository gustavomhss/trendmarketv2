import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from services.auto_resolution.service import (  # noqa: E402
    AutoResolutionService,
    ResolutionConflictError,
)


def build_service(tmp_path: Path) -> AutoResolutionService:
    return AutoResolutionService(
        audit_log=tmp_path / "audit.jsonl",
        event_log=tmp_path / "events.jsonl",
        metrics_log=tmp_path / "metrics.jsonl",
    )


def test_auto_resolution_success(tmp_path: Path) -> None:
    service = build_service(tmp_path)
    result = service.apply(
        event_id="evt-1",
        symbol="BRLUSD",
        truth={"value": 5.43, "source": "truth_feed", "ts": 1700000000},
        quorum={"value": 5.4305, "quorum_ok": True, "diverg_pct": 0.004, "staleness_ms": 800},
        actor="auto_resolver",
        role="system",
    )

    assert result["outcome"] == "applied"
    audit_entries = service.load_audit_entries()
    assert len(audit_entries) == 1
    assert audit_entries[0]["action"] == "resolve.auto"
    metrics = service.load_metrics_entries()
    assert metrics[0]["quorum_ok"] is True
    assert metrics[0]["truth_rule_ok"] is True


def test_auto_resolution_requires_manual_when_divergent(tmp_path: Path) -> None:
    service = build_service(tmp_path)
    result = service.apply(
        event_id="evt-2",
        symbol="BRLUSD",
        truth={"value": 5.43, "source": "truth_feed", "ts": 1700000000},
        quorum={"value": 5.51, "quorum_ok": True, "diverg_pct": 0.02, "staleness_ms": 400},
        actor="auto_resolver",
        role="system",
    )

    assert result["outcome"] == "manual_required"
    audit_entries = service.load_audit_entries()
    assert audit_entries[0]["outcome"] == "manual_required"


def test_manual_override_requires_operator(tmp_path: Path) -> None:
    service = build_service(tmp_path)
    result = service.apply(
        event_id="evt-3",
        symbol="BRLUSD",
        truth={"value": 5.43, "source": "truth_feed", "ts": 1700000000},
        quorum={"value": 5.51, "quorum_ok": False, "diverg_pct": 0.02, "staleness_ms": 400},
        actor="operator_bot",
        role="operator",
        manual_decision="resolve_yes",
        reason="Verified settlement",
    )

    assert result["outcome"] == "applied_manual"
    audit_entries = service.load_audit_entries()
    assert audit_entries[0]["action"] == "resolve.manual"


def test_manual_override_denied_for_viewer(tmp_path: Path) -> None:
    service = build_service(tmp_path)
    try:
        service.apply(
            event_id="evt-4",
            symbol="BRLUSD",
            truth={"value": 5.43, "source": "truth_feed", "ts": 1700000000},
            quorum={"value": 5.43, "quorum_ok": True, "diverg_pct": 0.0, "staleness_ms": 100},
            actor="viewer",
            role="viewer",
            manual_decision="resolve_yes",
        )
    except PermissionError:
        pass
    else:
        raise AssertionError("viewer role should not override decisions")


def test_idempotency_returns_existing_decision(tmp_path: Path) -> None:
    service = build_service(tmp_path)
    first = service.apply(
        event_id="evt-5",
        symbol="BRLUSD",
        truth={"value": 1.0, "source": "truth_feed", "ts": 1700000000},
        quorum={"value": 1.0, "quorum_ok": True, "diverg_pct": 0.0, "staleness_ms": 10},
        actor="auto_resolver",
        role="system",
        idempotency_key="same",
    )
    second = service.apply(
        event_id="evt-5",
        symbol="BRLUSD",
        truth={"value": 1.0, "source": "truth_feed", "ts": 1700000000},
        quorum={"value": 1.0, "quorum_ok": True, "diverg_pct": 0.0, "staleness_ms": 10},
        actor="auto_resolver",
        role="system",
        idempotency_key="same",
    )

    assert first == second


def test_conflict_on_stale_resource_version(tmp_path: Path) -> None:
    service = build_service(tmp_path)
    result = service.apply(
        event_id="evt-6",
        symbol="BRLUSD",
        truth={"value": 5.43, "source": "truth_feed", "ts": 1700000000},
        quorum={"value": 5.4301, "quorum_ok": True, "diverg_pct": 0.001, "staleness_ms": 100},
        actor="auto_resolver",
        role="system",
    )

    try:
        service.apply(
            event_id="evt-6",
            symbol="BRLUSD",
            truth={"value": 5.4301, "source": "truth_feed", "ts": 1700000001},
            quorum={"value": 5.4302, "quorum_ok": True, "diverg_pct": 0.001, "staleness_ms": 150},
            actor="auto_resolver",
            role="system",
            resource_version="v9999",
        )
    except ResolutionConflictError:
        pass
    else:
        raise AssertionError("expected conflict on stale resource version")

    assert result["decision_id"]
