"""Thin API handler for `/resolve/apply` requests."""
from __future__ import annotations

from typing import Any, Dict, Mapping, Optional
import time

from .service import (
    AutoResolutionService,
    ResolutionRecord,
    TruthSourceSignal,
)


def apply_resolution(payload: Mapping[str, Any], *, service: AutoResolutionService) -> Dict[str, Any]:
    """Process a `/resolve/apply` request using the provided service."""

    required_fields = {"event_id", "actor", "role", "idempotency_key"}
    missing = required_fields - payload.keys()
    if missing:
        missing_str = ", ".join(sorted(missing))
        raise ValueError(f"Missing required fields: {missing_str}")

    quorum_input = _resolve_quorum(payload)
    truth_source_signal = _build_truth_source(payload.get("truth_source"))

    resource_version = payload.get("resource_version")
    resource_version_value: Optional[int]
    if resource_version is None:
        resource_version_value = None
    else:
        resource_version_value = int(resource_version)

    record = service.apply(
        event_id=str(payload["event_id"]),
        quorum_votes=quorum_input,
        actor=str(payload["actor"]),
        role=str(payload["role"]),
        idempotency_key=str(payload["idempotency_key"]),
        trace_id=payload.get("trace_id"),
        truth_source=truth_source_signal,
        manual_override=payload.get("manual_override"),
        manual_reason=payload.get("manual_reason"),
        evidence_uri=payload.get("evidence_uri"),
        resource_version=resource_version_value,
    )
    return _format_response(record)


def _resolve_quorum(payload: Mapping[str, Any]) -> Any:
    if "quorum" in payload:
        return payload["quorum"]
    if "quorum_votes" in payload:
        votes = payload["quorum_votes"]
        if isinstance(votes, (list, tuple)):
            return [str(vote) for vote in votes]
    raise ValueError("Request must include `quorum` or `quorum_votes`")


def _build_truth_source(data: Optional[Mapping[str, Any]]) -> Optional[TruthSourceSignal]:
    if not data:
        return None
    observed_at = data.get("observed_at") or time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    return TruthSourceSignal(
        source=str(data.get("source", "unknown")),
        verdict=str(data.get("verdict", "")).lower(),
        confidence=float(data.get("confidence", 0.0)),
        observed_at=str(observed_at),
        evidence_uri=data.get("evidence_uri"),
        notes=data.get("notes"),
    )


def _format_response(record: ResolutionRecord) -> Dict[str, Any]:
    return {
        "decision_id": record.trace_id,
        "outcome": record.outcome,
        "reason": record.reason,
        "quorum_ok": record.quorum_ok,
        "truth_source_used": record.truth_source_used,
        "manual_override": record.manual_override,
        "resource_version": record.resource_version,
        "agreement_score": record.agreement_score,
    }


__all__ = ["apply_resolution"]
