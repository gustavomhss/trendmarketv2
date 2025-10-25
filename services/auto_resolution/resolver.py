"""Auto-resolution service with Sprint 5 decision rules and audit logging."""
from __future__ import annotations

from dataclasses import asdict, dataclass
from hashlib import sha256
from pathlib import Path
from typing import Dict, Iterable, List, Optional
import json
import time
import uuid

ALLOWED_RESOLUTION_ROLES = {"resolver", "admin"}


class IdempotencyKeyConflict(RuntimeError):
    """Raised when an idempotency key is reused with mismatched payloads."""

    def __init__(self, key: str) -> None:
        super().__init__(f"Idempotency key '{key}' conflict")
        self.key = key


class DecisionConflict(RuntimeError):
    """Raised when a decision has already been recorded with another outcome."""

    def __init__(self, decision_id: str) -> None:
        super().__init__(f"Decision '{decision_id}' conflict")
        self.decision_id = decision_id


class DecisionRule:
    """Enumeration of Sprint 5 auto-resolution decision rules."""

    TRUTH_SOURCE_FINAL = "truth_source_final"
    TRUTH_SOURCE_OVERRIDE = "truth_source_override"
    QUORUM_CONSENSUS = "quorum_consensus"
    MANUAL_OVERRIDE = "manual_override"
    MANUAL_REVIEW = "manual_review_required"


@dataclass(frozen=True)
class TruthSourcePayload:
    """Structured payload emitted by an authoritative truth source."""

    source: str
    status: str
    verdict: Optional[str]
    confidence: float
    ts: Optional[str] = None
    evidence_uri: Optional[str] = None

    def is_final(self) -> bool:
        """Return ``True`` when the truth source payload is considered final."""

        return self.status.lower() in {"final", "confirmed"}


@dataclass(frozen=True)
class QuorumEvaluation:
    """Result of quorum aggregation for the disputed market."""

    quorum_ok: bool
    suggested_outcome: Optional[str]
    confidence: Optional[float] = None
    contributors: Optional[List[str]] = None


@dataclass(frozen=True)
class ManualOverride:
    """Manual override supplied by a human operator."""

    outcome: str
    reason: Optional[str] = None


@dataclass
class AutoResolutionDecision:
    """Decision emitted by :class:`AutoResolutionService`."""

    decision_id: str
    outcome: str
    rule: str
    trace_id: str
    actor: str
    role: str
    idempotency_key: str
    metadata: Dict[str, object]

    def as_dict(self) -> Dict[str, object]:
        return {
            "decision_id": self.decision_id,
            "outcome": self.outcome,
            "rule": self.rule,
            "trace_id": self.trace_id,
        }


@dataclass
class _StoredDecision:
    decision: AutoResolutionDecision
    payload_hash: str


class AutoResolutionService:
    """Apply Sprint 5 auto-resolution rules with RBAC and audit trail."""

    def __init__(self, audit_log: Path, *, allowed_roles: Optional[Iterable[str]] = None) -> None:
        self.audit_log = audit_log
        self.audit_log.parent.mkdir(parents=True, exist_ok=True)
        self.allowed_roles = set(allowed_roles) if allowed_roles else ALLOWED_RESOLUTION_ROLES
        self._idempotency: Dict[str, _StoredDecision] = {}
        self._decisions: Dict[str, AutoResolutionDecision] = {}

    def apply_resolution(
        self,
        *,
        decision_id: str,
        truth_payload: TruthSourcePayload,
        quorum_result: QuorumEvaluation,
        actor: str,
        role: str,
        idempotency_key: str,
        manual_override: Optional[ManualOverride] = None,
        metadata: Optional[Dict[str, object]] = None,
        trace_id: Optional[str] = None,
    ) -> AutoResolutionDecision:
        self._enforce_role(role)

        resolved_metadata = dict(metadata or {})
        payload_hash = self._compute_payload_hash(
            decision_id=decision_id,
            truth_payload=truth_payload,
            quorum_result=quorum_result,
            manual_override=manual_override,
            metadata=resolved_metadata,
        )

        if idempotency_key in self._idempotency:
            stored = self._idempotency[idempotency_key]
            if stored.payload_hash != payload_hash:
                raise IdempotencyKeyConflict(idempotency_key)
            return stored.decision

        outcome, rule = self._determine_outcome(truth_payload, quorum_result, manual_override)

        resolved_trace = trace_id or uuid.uuid4().hex
        decision = AutoResolutionDecision(
            decision_id=decision_id,
            outcome=outcome,
            rule=rule,
            trace_id=resolved_trace,
            actor=actor,
            role=role,
            idempotency_key=idempotency_key,
            metadata=resolved_metadata,
        )

        if decision_id in self._decisions:
            previous = self._decisions[decision_id]
            if previous.outcome != decision.outcome or previous.rule != decision.rule:
                raise DecisionConflict(decision_id)
            # Reuse previous decision for deterministic trace id
            decision.trace_id = previous.trace_id
            self._idempotency[idempotency_key] = _StoredDecision(decision=previous, payload_hash=payload_hash)
            return previous

        self._append_audit(
            actor=actor,
            role=role,
            decision=decision,
            truth_payload=truth_payload,
            quorum_result=quorum_result,
            manual_override=manual_override,
            payload_hash=payload_hash,
        )

        self._decisions[decision_id] = decision
        self._idempotency[idempotency_key] = _StoredDecision(decision=decision, payload_hash=payload_hash)
        return decision

    def load_audit_entries(self) -> List[Dict[str, object]]:
        if not self.audit_log.exists():
            return []
        with self.audit_log.open("r", encoding="utf-8") as handle:
            return [json.loads(line) for line in handle if line.strip()]

    def _determine_outcome(
        self,
        truth_payload: TruthSourcePayload,
        quorum_result: QuorumEvaluation,
        manual_override: Optional[ManualOverride],
    ) -> (str, str):
        if manual_override is not None:
            return manual_override.outcome, DecisionRule.MANUAL_OVERRIDE

        truth_verdict = truth_payload.verdict
        truth_final = truth_payload.is_final() and truth_verdict is not None
        quorum_ok = quorum_result.quorum_ok and quorum_result.suggested_outcome is not None

        if truth_final:
            if quorum_ok and quorum_result.suggested_outcome != truth_verdict:
                return truth_verdict, DecisionRule.TRUTH_SOURCE_OVERRIDE
            return truth_verdict, DecisionRule.TRUTH_SOURCE_FINAL

        if quorum_ok:
            return quorum_result.suggested_outcome or "manual_review", DecisionRule.QUORUM_CONSENSUS

        return "manual_review", DecisionRule.MANUAL_REVIEW

    def _compute_payload_hash(
        self,
        *,
        decision_id: str,
        truth_payload: TruthSourcePayload,
        quorum_result: QuorumEvaluation,
        manual_override: Optional[ManualOverride],
        metadata: Dict[str, object],
    ) -> str:
        canonical = {
            "decision_id": decision_id,
            "truth_payload": asdict(truth_payload),
            "quorum_result": asdict(quorum_result),
            "manual_override": asdict(manual_override) if manual_override else None,
            "metadata": metadata,
        }
        payload = json.dumps(canonical, sort_keys=True, default=str)
        return sha256(payload.encode("utf-8")).hexdigest()

    def _append_audit(
        self,
        *,
        actor: str,
        role: str,
        decision: AutoResolutionDecision,
        truth_payload: TruthSourcePayload,
        quorum_result: QuorumEvaluation,
        manual_override: Optional[ManualOverride],
        payload_hash: str,
    ) -> None:
        ts_iso = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
        entry = {
            "ts": ts_iso,
            "actor": actor,
            "role": role,
            "action": "resolve",
            "target": decision.decision_id,
            "payload_hash": payload_hash,
            "trace_id": decision.trace_id,
            "outcome": decision.outcome,
            "rule": decision.rule,
            "truth_source": truth_payload.source,
            "truth_status": truth_payload.status,
            "quorum_ok": quorum_result.quorum_ok,
        }
        if truth_payload.verdict is not None:
            entry["truth_verdict"] = truth_payload.verdict
        if manual_override is not None:
            entry["manual_override"] = manual_override.reason or True
        if decision.metadata:
            entry["metadata"] = decision.metadata
        with self.audit_log.open("a", encoding="utf-8") as handle:
            handle.write(json.dumps(entry) + "\n")

    def _enforce_role(self, role: str) -> None:
        if role not in self.allowed_roles:
            raise PermissionError(f"Role '{role}' not permitted to resolve decisions")


__all__ = [
    "ALLOWED_RESOLUTION_ROLES",
    "AutoResolutionDecision",
    "AutoResolutionService",
    "DecisionConflict",
    "DecisionRule",
    "IdempotencyKeyConflict",
    "ManualOverride",
    "QuorumEvaluation",
    "TruthSourcePayload",
]
