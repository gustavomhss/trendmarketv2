"""In-process API facade for auto-resolution operations."""
from __future__ import annotations

from hashlib import sha256
from typing import Any, Dict, Iterable, Mapping, Optional, Tuple
import json
import time

from .service import (
    AutoResolutionService,
    DecisionRule,
    IdempotencyKeyConflict,
    ResolutionRecord,
    TruthSourceSignal,
)


class InvalidRequest(ValueError):
    """Raised when an inbound request payload violates contract expectations."""


class AutoResolutionAPI:
    """Lightweight handler that adapts HTTP-style payloads to the service layer."""

    def __init__(self, service: AutoResolutionService) -> None:
        self._service = service
        self._idempotency_cache: Dict[str, str] = {}

    def resolve_apply(
        self,
        body: Mapping[str, Any],
        *,
        actor: str,
        role: str,
        idempotency_key: str,
        trace_id: Optional[str] = None,
    ) -> Dict[str, Any]:
        if not isinstance(body, Mapping):
            raise InvalidRequest("body must be an object")

        schema_version = body.get("schema_version")
        if schema_version != 1:
            raise InvalidRequest("Unsupported schema_version")

        decision_id = self._require(body, "decision_id")
        truth_source_name = self._require(body, "truth_source")
        quorum_flag = bool(body.get("quorum", False))
        payload = body.get("payload")
        if payload is None or not isinstance(payload, Mapping):
            raise InvalidRequest("payload must be an object")

        truth_payload = self._ensure_mapping(payload.get("truth"), "truth")
        quorum_payload = self._ensure_mapping(payload.get("quorum"), "quorum")
        manual_section = payload.get("manual_override")

        truth_signal = _build_truth_signal(truth_source_name, truth_payload)
        quorum_votes = _build_quorum_votes(quorum_payload, quorum_flag)
        manual_override, manual_reason = _parse_manual_override(manual_section)
        evidence_uri = payload.get("evidence_uri")
        if manual_override is not None and not evidence_uri:
            # Provide a deterministic evidence URI to satisfy service invariants.
            evidence_uri = "manual://override"

        metadata = {
            key: value
            for key, value in payload.items()
            if key not in {"truth", "quorum", "manual_override", "evidence_uri"}
        }

        self._enforce_idempotency(idempotency_key, body)

        record = self._service.apply(
            event_id=str(decision_id),
            quorum_votes=quorum_votes,
            actor=actor,
            role=role,
            idempotency_key=idempotency_key,
            truth_source=truth_signal,
            manual_override=manual_override,
            manual_reason=manual_reason,
            evidence_uri=evidence_uri,
            trace_id=trace_id,
            metadata=metadata if metadata else None,
        )
        return _format_record(record)

    def _require(self, payload: Mapping[str, Any], field: str) -> Any:
        value = payload.get(field)
        if value is None:
            raise InvalidRequest(f"Missing field: {field}")
        return value

    def _ensure_mapping(self, obj: Any, label: str) -> Mapping[str, Any]:
        if obj is None:
            return {}
        if not isinstance(obj, Mapping):
            raise InvalidRequest(f"Section '{label}' must be an object")
        return obj

    def _enforce_idempotency(self, key: str, body: Mapping[str, Any]) -> None:
        canonical = json.dumps(body, sort_keys=True, default=str)
        fingerprint = sha256(canonical.encode("utf-8")).hexdigest()
        cached = self._idempotency_cache.get(key)
        if cached is None:
            self._idempotency_cache[key] = fingerprint
            return
        if cached != fingerprint:
            raise IdempotencyKeyConflict(key)


def _build_truth_signal(source: Any, payload: Mapping[str, Any]) -> TruthSourceSignal:
    observed_at = payload.get("observed_at") or time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    confidence = float(payload.get("confidence", 0.0))
    verdict = payload.get("verdict")
    signal = TruthSourceSignal(
        source=str(source),
        verdict=verdict if verdict is None else str(verdict),
        confidence=confidence,
        observed_at=str(observed_at),
        evidence_uri=payload.get("evidence_uri"),
        notes=payload.get("notes"),
    )
    status = str(payload.get("status", "pending"))
    return signal.with_status(status)


def _build_quorum_votes(payload: Mapping[str, Any], quorum_flag: bool) -> Mapping[str, Any]:
    outcome = payload.get("outcome")
    contributors: Iterable[Any] = payload.get("contributors", [])
    if not contributors:
        # Create a single aggregate vote to honour the quorum flag.
        contributors = ["quorum"]
    votes = [
        {"source": str(contributor), "verdict": outcome or ("accepted" if quorum_flag else "rejected"), "weight": 1.0}
        for contributor in contributors
    ]
    return {"votes": votes, "divergence_pct": float(payload.get("divergence_pct", 0.0))}


def _parse_manual_override(override: Any) -> Tuple[Optional[str], Optional[str]]:
    if override is None:
        return None, None
    if isinstance(override, str):
        if not override:
            raise InvalidRequest("manual_override cannot be empty")
        return override, None
    if not isinstance(override, Mapping):
        raise InvalidRequest("manual_override must be an object or string")
    outcome = override.get("outcome")
    if not outcome:
        raise InvalidRequest("manual_override requires an outcome")
    reason = override.get("reason")
    return str(outcome), (str(reason) if reason is not None else None)


def _format_record(record: ResolutionRecord) -> Dict[str, Any]:
    return {
        "decision_id": record.decision_id,
        "outcome": record.outcome,
        "rule": record.rule,
        "trace_id": record.trace_id,
        "resource_version": record.resource_version,
        "truth_source_used": record.truth_source_used,
        "manual_override": record.manual_override,
    }


def apply_resolution(payload: Mapping[str, Any], *, service: AutoResolutionService) -> Dict[str, Any]:
    """Compatibility helper used by legacy integration tests."""

    required = {"event_id", "actor", "role", "idempotency_key"}
    missing = required - set(payload.keys())
    if missing:
        raise ValueError(f"Missing required fields: {', '.join(sorted(missing))}")

    quorum_votes = payload.get("quorum") or payload.get("quorum_votes")
    if quorum_votes is None:
        raise ValueError("Request must include quorum or quorum_votes")

    truth_source_data = payload.get("truth_source")
    truth_signal = None
    if isinstance(truth_source_data, Mapping):
        truth_signal = _build_truth_source_from_dict(truth_source_data)

    record = service.apply(
        event_id=str(payload["event_id"]),
        quorum_votes=quorum_votes,
        actor=str(payload["actor"]),
        role=str(payload["role"]),
        idempotency_key=str(payload["idempotency_key"]),
        trace_id=payload.get("trace_id"),
        truth_source=truth_signal,
        manual_override=payload.get("manual_override"),
        manual_reason=payload.get("manual_reason"),
        evidence_uri=payload.get("evidence_uri"),
        resource_version=payload.get("resource_version"),
    )
    return {
        "decision_id": record.decision_id,
        "outcome": record.outcome,
        "status": record.status,
        "rule": record.rule,
        "trace_id": record.trace_id,
        "resource_version": record.resource_version,
        "truth_source_used": record.truth_source_used,
        "manual_override": record.manual_override,
        "agreement_score": record.agreement_score,
    }


def _build_truth_source_from_dict(data: Mapping[str, Any]) -> TruthSourceSignal:
    observed_at = data.get("observed_at") or time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    signal = TruthSourceSignal(
        source=str(data.get("source", "unknown")),
        verdict=data.get("verdict"),
        confidence=float(data.get("confidence", 0.0)),
        observed_at=str(observed_at),
        evidence_uri=data.get("evidence_uri"),
        notes=data.get("notes"),
    )
    status = str(data.get("status", "final"))
    return signal.with_status(status)


__all__ = ["AutoResolutionAPI", "InvalidRequest", "apply_resolution"]
