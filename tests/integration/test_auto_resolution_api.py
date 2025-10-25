import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

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
