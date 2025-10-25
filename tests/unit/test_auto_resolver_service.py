import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from services.resolution.service import AutoResolverService, DecisionConflictError  # noqa: E402


def test_apply_with_quorum_creates_resolution():
    service = AutoResolverService()

    result = service.apply_decision(
        schema_version=1,
        decision_id="dec-1",
        truth_source="truth_a",
        quorum=True,
        payload={"score": 0.92},
    )

    assert result["outcome"] == "applied"
    record = service.get_resolution("dec-1")
    assert record.outcome == "applied"
    assert record.truth_source == "truth_a"
    assert service.backlog_total == 0


def test_queue_then_finalize_reuses_trace_and_updates_backlog():
    service = AutoResolverService()

    queued = service.apply_decision(
        schema_version=1,
        decision_id="dec-2",
        truth_source="truth_a",
        quorum=False,
        payload={"reason": "insufficient quorum"},
    )

    assert queued["outcome"] == "queued"
    assert service.backlog_total == 1
    assert service.backlog_for_source("truth_a") == 1

    resolved = service.finalize("dec-2", accepted=True, reason="manual override")

    assert resolved.outcome == "applied"
    assert resolved.trace_id == queued["trace_id"]
    assert "manual override" in resolved.payload.get("finalized_reason", "")
    assert service.backlog_total == 0


def test_duplicate_decision_raises_conflict():
    service = AutoResolverService()
    service.apply_decision(
        schema_version=1,
        decision_id="dec-3",
        truth_source="truth_a",
        quorum=True,
    )

    with pytest.raises(DecisionConflictError):
        service.apply_decision(
            schema_version=1,
            decision_id="dec-3",
            truth_source="truth_a",
            quorum=True,
        )
