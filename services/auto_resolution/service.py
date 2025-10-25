"""Auto-resolution service combining quorum evaluation and truth-source overrides."""
from __future__ import annotations

from dataclasses import dataclass, asdict
from hashlib import sha256
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Sequence
import json
import time
import uuid

ALLOWED_AUTO_ROLES = {"resolver", "admin", "resolver_lead"}
ALLOWED_MANUAL_ROLES = {"admin", "resolver_lead"}


RESOLVE_DECISION_SCHEMA_VERSION = 1


class ResolutionError(RuntimeError):
    """Raised when a resolution cannot be applied automatically."""


@dataclass
class TruthSourceSignal:
    """Signal reported by the configured truth source."""

    source: str
    verdict: str
    confidence: float
    observed_at: str
    evidence_uri: Optional[str] = None
    notes: Optional[str] = None

    def __post_init__(self) -> None:
        self.verdict = self.verdict.lower()
        if self.verdict not in {"accepted", "rejected"}:
            raise ValueError("Truth source verdict must be 'accepted' or 'rejected'")
        if not (0.0 <= self.confidence <= 1.0):
            raise ValueError("Truth source confidence must be between 0.0 and 1.0")


@dataclass
class ResolutionRecord:
    """Outcome of an auto-resolution attempt."""

    event_id: str
    outcome: str
    reason: str
    trace_id: str
    decided_at: float
    idempotency_key: str
    quorum_ok: bool
    truth_source_used: bool
    manual_override: bool


class AutoResolutionService:
    """Evaluate quorum decisions with truth-source overrides and audit logging."""

    def __init__(
        self,
        *,
        audit_log: Path,
        quorum_threshold: float = 2 / 3,
        truth_confidence_threshold: float = 0.7,
    ) -> None:
        self.audit_log = audit_log
        self.audit_log.parent.mkdir(parents=True, exist_ok=True)
        self.decision_log = self.audit_log.parent / "resolve_decisions.jsonl"
        self.quorum_threshold = quorum_threshold
        self.truth_confidence_threshold = truth_confidence_threshold
        self._idempotency: Dict[str, ResolutionRecord] = {}

    def apply(
        self,
        *,
        event_id: str,
        quorum_votes: Sequence[str],
        actor: str,
        role: str,
        idempotency_key: str,
        trace_id: Optional[str] = None,
        truth_source: Optional[TruthSourceSignal] = None,
        manual_override: Optional[str] = None,
        manual_reason: Optional[str] = None,
        evidence_uri: Optional[str] = None,
    ) -> ResolutionRecord:
        self._require_idempotency_key(idempotency_key)
        existing = self._idempotency.get(idempotency_key)
        if existing is not None:
            if existing.event_id != event_id:
                raise ResolutionError("Idempotency key reuse for different event is not allowed")
            return existing

        normalized_votes = [vote.lower() for vote in quorum_votes]
        self._enforce_role(role, ALLOWED_AUTO_ROLES, action="apply resolution")

        if manual_override is not None:
            self._enforce_role(role, ALLOWED_MANUAL_ROLES, action="perform manual override")
            outcome, truth_used, reason = self._apply_manual_override(manual_override, manual_reason)
            manual_flag = True
            quorum_ok = self._quorum_reached(normalized_votes)
        else:
            manual_flag = False
            outcome, truth_used, reason, quorum_ok = self._apply_auto_logic(
                normalized_votes, truth_source
            )

        decided_at = time.time()
        resolved_trace = trace_id or uuid.uuid4().hex
        record = ResolutionRecord(
            event_id=event_id,
            outcome=outcome,
            reason=reason,
            trace_id=resolved_trace,
            decided_at=decided_at,
            idempotency_key=idempotency_key,
            quorum_ok=quorum_ok,
            truth_source_used=truth_used,
            manual_override=manual_flag,
        )
        self._idempotency[idempotency_key] = record
        self._append_audit(
            actor=actor,
            role=role,
            record=record,
            quorum_votes=normalized_votes,
            truth_source=truth_source,
            manual_reason=manual_reason,
            evidence_uri=evidence_uri,
        )
        return record

    def _apply_manual_override(
        self, manual_override: str, manual_reason: Optional[str]
    ) -> tuple[str, bool, str]:
        normalized = manual_override.lower()
        if normalized not in {"accepted", "rejected"}:
            raise ValueError("Manual override must be 'accepted' or 'rejected'")
        reason = manual_reason or "manual_override"
        return normalized, False, reason

    def _apply_auto_logic(
        self, quorum_votes: Sequence[str], truth_source: Optional[TruthSourceSignal]
    ) -> tuple[str, bool, str, bool]:
        quorum_ok = self._quorum_reached(quorum_votes)
        majority_accepts = self._majority_accepts(quorum_votes)

        if truth_source and truth_source.confidence >= self.truth_confidence_threshold:
            return truth_source.verdict, True, f"truth_source:{truth_source.source}", quorum_ok

        if quorum_ok:
            reason = "quorum"
            outcome = "accepted" if majority_accepts else "rejected"
            return outcome, False, reason, quorum_ok

        raise ResolutionError(
            "Quorum not reached and no reliable truth source or manual override provided"
        )

    def _append_audit(
        self,
        *,
        actor: str,
        role: str,
        record: ResolutionRecord,
        quorum_votes: Sequence[str],
        truth_source: Optional[TruthSourceSignal],
        manual_reason: Optional[str],
        evidence_uri: Optional[str],
    ) -> None:
        ts_iso = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime(record.decided_at))
        event = self._build_decision_event(
            ts_iso=ts_iso,
            actor=actor,
            role=role,
            record=record,
            quorum_votes=quorum_votes,
            truth_source=truth_source,
            evidence_uri=evidence_uri,
        )
        self._write_decision_event(event)
        payload = {
            "event_id": record.event_id,
            "quorum_votes": list(quorum_votes),
            "truth_source": asdict(truth_source) if truth_source else None,
            "outcome": record.outcome,
            "reason": record.reason,
            "manual_reason": manual_reason,
            "evidence_uri": evidence_uri,
            "idempotency_key": record.idempotency_key,
        }
        payload_hash = sha256(json.dumps(payload, sort_keys=True).encode("utf-8")).hexdigest()
        entry = {
            "ts": ts_iso,
            "actor": actor,
            "role": role,
            "action": "auto_resolve.apply",
            "target": record.event_id,
            "payload_hash": payload_hash,
            "trace_id": record.trace_id,
            "outcome": record.outcome,
            "idempotency_key": record.idempotency_key,
            "manual_override": record.manual_override,
            "truth_source_used": record.truth_source_used,
            "quorum_ok": record.quorum_ok,
        }
        with self.audit_log.open("a", encoding="utf-8") as fh:
            fh.write(json.dumps(entry) + "\n")

    def _quorum_reached(self, votes: Sequence[str]) -> bool:
        if not votes:
            return False
        support = sum(1 for vote in votes if vote == "accepted")
        ratio = support / len(votes)
        return ratio >= self.quorum_threshold

    def _build_decision_event(
        self,
        *,
        ts_iso: str,
        actor: str,
        role: str,
        record: ResolutionRecord,
        quorum_votes: Sequence[str],
        truth_source: Optional[TruthSourceSignal],
        evidence_uri: Optional[str],
    ) -> Dict[str, object]:
        rule = "auto.quorum"
        if record.manual_override:
            rule = "manual.override"
        elif record.truth_source_used:
            source = truth_source.source if truth_source else "unknown"
            normalized_source = source.replace(" ", "_").lower()
            rule = f"truth_source.{normalized_source}"

        truth_payload = asdict(truth_source) if truth_source else None
        event: Dict[str, object] = {
            "schema_version": RESOLVE_DECISION_SCHEMA_VERSION,
            "ts": ts_iso,
            "event_id": record.event_id,
            "rule": rule,
            "decision": record.outcome,
            "actor": actor,
            "role": role,
            "trace_id": record.trace_id,
            "reason": record.reason,
            "manual_override": record.manual_override,
            "truth_source_used": record.truth_source_used,
            "quorum_ok": record.quorum_ok,
            "quorum_votes": list(quorum_votes),
            "truth_source": truth_payload,
            "evidence_uri": evidence_uri,
            "idempotency_key": record.idempotency_key,
        }
        return event

    def _write_decision_event(self, event: Dict[str, object]) -> None:
        self.decision_log.parent.mkdir(parents=True, exist_ok=True)
        with self.decision_log.open("a", encoding="utf-8") as fh:
            fh.write(json.dumps(event) + "\n")

    def load_decision_events(self) -> List[Dict[str, object]]:
        if not self.decision_log.exists():
            return []
        with self.decision_log.open("r", encoding="utf-8") as fh:
            return [json.loads(line) for line in fh if line.strip()]

    def _majority_accepts(self, votes: Sequence[str]) -> bool:
        support = sum(1 for vote in votes if vote == "accepted")
        return support >= (len(votes) - support)

    def _enforce_role(self, role: str, allowed: Iterable[str], *, action: str) -> None:
        if role not in allowed:
            raise PermissionError(f"Role '{role}' not permitted to {action}")

    def _require_idempotency_key(self, key: str) -> None:
        if not key or len(key) < 8:
            raise ValueError("idempotency_key must be at least 8 characters long")

    def load_audit_entries(self) -> List[Dict[str, object]]:
        if not self.audit_log.exists():
            return []
        with self.audit_log.open("r", encoding="utf-8") as fh:
            return [json.loads(line) for line in fh if line.strip()]


__all__ = [
    "ALLOWED_AUTO_ROLES",
    "ALLOWED_MANUAL_ROLES",
    "AutoResolutionService",
    "ResolutionError",
    "ResolutionRecord",
    "TruthSourceSignal",
]
