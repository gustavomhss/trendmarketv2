"""HTTP-style API wrapper for the auto-resolution service."""
from __future__ import annotations

from typing import Any, Dict, Iterable

from .service import AutoResolutionService


class InvalidRequest(ValueError):
    """Raised when an inbound request payload is invalid."""


_REQUIRED_FIELDS: Iterable[str] = (
    "event_id",
    "symbol",
    "truth",
    "quorum",
    "actor",
    "role",
)


class AutoResolutionAPI:
    """Thin validation layer delegating to :class:`AutoResolutionService`."""

    def __init__(self, service: AutoResolutionService) -> None:
        self._service = service

    def apply(self, payload: Dict[str, Any]) -> Dict[str, str]:
        if not isinstance(payload, dict):
            raise InvalidRequest("payload must be a JSON object")

        missing = [field for field in _REQUIRED_FIELDS if field not in payload]
        if missing:
            joined = ", ".join(sorted(missing))
            raise InvalidRequest(f"missing required fields: {joined}")

        truth = payload["truth"]
        quorum = payload["quorum"]
        if not isinstance(truth, dict):
            raise InvalidRequest("truth must be an object")
        if not isinstance(quorum, dict):
            raise InvalidRequest("quorum must be an object")

        response = self._service.apply(
            event_id=str(payload["event_id"]),
            symbol=str(payload["symbol"]),
            truth=truth,
            quorum=quorum,
            actor=str(payload["actor"]),
            role=str(payload["role"]),
            idempotency_key=payload.get("idempotency_key"),
            manual_decision=payload.get("manual_decision"),
            reason=payload.get("reason"),
            trace_id=payload.get("trace_id"),
            resource_version=payload.get("resource_version"),
        )
        return response


__all__ = ["AutoResolutionAPI", "InvalidRequest"]
"""In-process API facade for the auto-resolution service."""
from __future__ import annotations

from typing import Dict, Mapping, Optional

from .resolver import (
    AutoResolutionDecision,
    AutoResolutionService,
    ManualOverride,
    QuorumEvaluation,
    TruthSourcePayload,
)


class InvalidRequest(ValueError):
    """Raised when the incoming payload violates API expectations."""


class AutoResolutionAPI:
    """Lightweight handler exposing ``/resolve/apply`` semantics."""

    def __init__(self, service: AutoResolutionService) -> None:
        self.service = service

    def resolve_apply(
        self,
        body: Mapping[str, object],
        *,
        actor: str,
        role: str,
        idempotency_key: str,
        trace_id: Optional[str] = None,
    ) -> Dict[str, object]:
        schema_version = body.get("schema_version")
        if schema_version != 1:
            raise InvalidRequest("Unsupported schema_version")

        decision_id = self._require_field(body, "decision_id")
        truth_source_name = self._require_field(body, "truth_source")
        quorum_flag = bool(body.get("quorum", False))
        payload_obj = body.get("payload") or {}

        truth_section = self._ensure_mapping(payload_obj.get("truth"), "truth")
        quorum_section = self._ensure_mapping(payload_obj.get("quorum"), "quorum")
        manual_override_section = payload_obj.get("manual_override")

        truth_payload = TruthSourcePayload(
            source=str(truth_source_name),
            status=str(truth_section.get("status", "pending")),
            verdict=truth_section.get("verdict"),
            confidence=float(truth_section.get("confidence", 0.0)),
            ts=truth_section.get("ts"),
            evidence_uri=truth_section.get("evidence_uri"),
        )

        quorum_result = QuorumEvaluation(
            quorum_ok=quorum_flag,
            suggested_outcome=quorum_section.get("outcome"),
            confidence=self._optional_float(quorum_section.get("confidence")),
            contributors=list(quorum_section.get("contributors", [])),
        )

        manual_override = self._parse_manual_override(manual_override_section)

        metadata = {
            key: value
            for key, value in payload_obj.items()
            if key not in {"truth", "quorum", "manual_override"}
        }

        decision: AutoResolutionDecision = self.service.apply_resolution(
            decision_id=decision_id,
            truth_payload=truth_payload,
            quorum_result=quorum_result,
            actor=actor,
            role=role,
            idempotency_key=idempotency_key,
            manual_override=manual_override,
            metadata=metadata,
            trace_id=trace_id,
        )
        return decision.as_dict()

    def _require_field(self, payload: Mapping[str, object], field: str) -> object:
        value = payload.get(field)
        if value is None:
            raise InvalidRequest(f"Missing field: {field}")
        return value

    def _ensure_mapping(self, obj: object, field: str) -> Mapping[str, object]:
        if obj is None:
            return {}
        if not isinstance(obj, Mapping):
            raise InvalidRequest(f"Section '{field}' must be an object")
        return obj

    def _parse_manual_override(self, override: object) -> Optional[ManualOverride]:
        if override is None:
            return None
        if isinstance(override, str):
            if not override:
                raise InvalidRequest("manual_override outcome cannot be empty")
            return ManualOverride(outcome=override)
        if not isinstance(override, Mapping):
            raise InvalidRequest("manual_override must be an object or string")
        outcome = override.get("outcome")
        if not outcome:
            raise InvalidRequest("manual_override requires an outcome")
        reason = override.get("reason")
        return ManualOverride(outcome=str(outcome), reason=str(reason) if reason is not None else None)

    def _optional_float(self, value: object) -> Optional[float]:
        if value is None:
            return None
        return float(value)


__all__ = ["AutoResolutionAPI", "InvalidRequest"]
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
