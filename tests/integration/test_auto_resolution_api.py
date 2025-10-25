import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from services.auto_resolution import AutoResolutionService, apply_resolution  # noqa: E402


def _service(tmp_path: Path) -> AutoResolutionService:
    base = tmp_path / "out" / "resolve"
    audit_path = base / "audit.log"
    metrics_path = base / "metrics.jsonl"
    return AutoResolutionService(audit_log=audit_path, metrics_log=metrics_path)


def _payload(base: dict | None = None) -> dict:
    payload = {
        "event_id": "evt-api-1",
        "quorum": {
            "votes": [
                {"source": "alpha", "verdict": "accepted", "weight": 1.0},
                {"source": "beta", "verdict": "accepted", "weight": 1.0},
                {"source": "gamma", "verdict": "rejected", "weight": 1.0},
            ],
            "divergence_pct": 0.003,
        },
        "actor": "zoe",
        "role": "operator",
        "idempotency_key": "idem-api-1234",
        "resource_version": 0,
    }
    if base:
        payload.update(base)
    return payload


def test_apply_resolution_handler_idempotency(tmp_path: Path) -> None:
    service = _service(tmp_path)
    payload = _payload()

    first = apply_resolution(payload, service=service)
    assert first["outcome"] == "accepted"
    assert first["decision_id"]
    assert first["truth_source_used"] is False
    assert first["resource_version"] == 1

    second = apply_resolution(payload, service=service)
    assert second == first

    entries = service.load_audit_entries()
    assert len(entries) == 1
    assert entries[0]["idempotency_key"] == "idem-api-1234"


def test_apply_resolution_manual_fallback(tmp_path: Path) -> None:
    service = _service(tmp_path)
    payload = _payload(
        {
            "event_id": "evt-api-2",
            "idempotency_key": "idem-api-5678",
            "manual_override": "rejected",
            "manual_reason": "insufficient quorum",
            "evidence_uri": "s3://bucket/proof",
            "role": "admin",
        }
    )

    result = apply_resolution(payload, service=service)
    assert result["outcome"] == "rejected"
    assert result["manual_override"] is True
    assert result["truth_source_used"] is False


def test_apply_resolution_requires_fields(tmp_path: Path) -> None:
    service = _service(tmp_path)
    with pytest.raises(ValueError):
        apply_resolution({"event_id": "evt"}, service=service)
