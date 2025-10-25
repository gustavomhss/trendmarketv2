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
