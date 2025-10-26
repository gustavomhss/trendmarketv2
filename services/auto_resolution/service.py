"""Auto-resolution service with RBAC, audit logging, and metrics."""
from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Dict, Iterable, List, Mapping, Optional, Sequence, Tuple
import json
import time
import uuid

from .telemetry import telemetry


ALLOWED_AUTO_ROLES = {"operator", "resolver", "admin", "system"}
ALLOWED_MANUAL_ROLES = {"admin", "resolver_lead"}
AGREEMENT_THRESHOLD = 0.6
RESOLVE_DECISION_SCHEMA_VERSION = 1
_DIVERGENCE_THRESHOLD = 0.01


class ResolutionError(RuntimeError):
    """Raised when a resolution cannot be completed automatically."""


class ResolutionConflictError(ResolutionError):
    """Raised when resource-version semantics detect a conflict."""

    def __init__(self, event_id: str, expected: int, provided: Optional[int]) -> None:
        message = (
            f"Conflict applying resolution for '{event_id}': expected resource_version {expected}, "
            f"got {provided}"
        )
        super().__init__(message)
        self.event_id = event_id
        self.expected = expected
        self.provided = provided


# Backwards compatibility alias expected by some tests.
ResolutionConflict = ResolutionConflictError


class IdempotencyKeyConflict(RuntimeError):
    """Raised when an idempotency key is reused with mismatched payloads."""

    def __init__(self, key: str) -> None:
        super().__init__(f"Idempotency key '{key}' conflict")
        self.key = key


class DecisionRule:
    """Canonical decision rules returned by the auto-resolution service."""

    TRUTH_SOURCE_FINAL = "truth_source_final"
    TRUTH_SOURCE_OVERRIDE = "truth_source_override"
    QUORUM_CONSENSUS = "quorum_consensus"
    MANUAL_OVERRIDE = "manual_override"
    MANUAL_REVIEW = "manual_review_required"


_FINAL_TRUTH_STATUSES = {"final", "confirmed", "resolved"}


@dataclass(frozen=True)
class TruthSourceSignal:
    """Structured payload emitted by a truth source."""

    source: str
    verdict: Optional[str]
    confidence: float
    observed_at: str
    evidence_uri: Optional[str] = None
    notes: Optional[str] = None

    def __post_init__(self) -> None:  # pragma: no cover - defensive validation
        object.__setattr__(self, "source", self.source.strip())
        if not self.source:
            raise ValueError("Truth source requires a non-empty source identifier")
        if self.verdict is not None:
            verdict = self.verdict.strip().lower()
            object.__setattr__(self, "verdict", verdict)
        if not (0.0 <= self.confidence <= 1.0):
            raise ValueError("Truth source confidence must be within [0.0, 1.0]")
        object.__setattr__(self, "observed_at", self.observed_at.strip())
        if not self.observed_at:
            raise ValueError("Truth source observed_at must be an ISO 8601 string")

    def is_final(self) -> bool:
        return (self.verdict is not None) and (self.status in _FINAL_TRUTH_STATUSES)

    @property
    def status(self) -> str:
        # ``observed_at`` already validated; allow callers to attach arbitrary status metadata
        return getattr(self, "_status", "final")

    def with_status(self, status: str) -> "TruthSourceSignal":
        clone = TruthSourceSignal(
            source=self.source,
            verdict=self.verdict,
            confidence=self.confidence,
            observed_at=self.observed_at,
            evidence_uri=self.evidence_uri,
            notes=self.notes,
        )
        object.__setattr__(clone, "_status", status.lower())
        return clone

    def to_event_payload(self) -> Dict[str, Any]:
        verdict = None if self.verdict is None else _as_event_decision(self.verdict)
        return {
            "source": self.source,
            "verdict": verdict,
            "confidence": self.confidence,
            "observed_at": self.observed_at,
            "evidence_uri": self.evidence_uri,
            "notes": self.notes,
        }


@dataclass
class ResolutionRecord:
    """Resolved decision returned by :class:`AutoResolutionService`."""

    event_id: str
    decision_id: str
    outcome: Optional[str]
    rule: str
    actor: str
    role: str
    trace_id: str
    decided_at: float
    idempotency_key: Optional[str]
    resource_version: int
    truth_source_used: bool
    manual_override: bool
    quorum_ok: bool
    agreement_score: float
    truth_verdict: Optional[str]
    manual_reason: Optional[str]
    evidence_uri: Optional[str]
    metadata: Dict[str, Any] = field(default_factory=dict)
    status: str = "applied"

    def as_dict(self) -> Dict[str, Any]:
        data = {
            "decision_id": self.decision_id,
            "outcome": self.status,
            "decision": self.outcome,
            "rule": self.rule,
            "trace_id": self.trace_id,
            "resource_version": self.resource_version,
            "idempotency_key": self.idempotency_key,
            "truth_source_used": self.truth_source_used,
            "manual_override": self.manual_override,
            "quorum_ok": self.quorum_ok,
            "agreement_score": self.agreement_score,
        }
        if self.manual_reason is not None:
            data["reason"] = self.manual_reason
        return data

    def __getitem__(self, key: str) -> Any:
        return self.as_dict()[key]


class AutoResolutionMetrics:
    """Helper persisting metrics about auto-resolution evaluations."""

    def __init__(self, metrics_log: Path) -> None:
        self.metrics_log = metrics_log
        self.metrics_log.parent.mkdir(parents=True, exist_ok=True)

    def emit(self, payload: Mapping[str, Any]) -> None:
        with self.metrics_log.open("a", encoding="utf-8") as handle:
            handle.write(json.dumps(dict(payload)) + "\n")


class AutoResolutionService:
    """Resolve events using quorum votes, truth signals, and manual overrides."""

    def __init__(
        self,
        *,
        audit_log: Path,
        event_log: Optional[Path] = None,
        metrics_log: Optional[Path] = None,
        divergence_threshold: float = _DIVERGENCE_THRESHOLD,
    ) -> None:
        self.audit_log = audit_log
        self.audit_log.parent.mkdir(parents=True, exist_ok=True)
        self.event_log = event_log or self.audit_log.parent / "resolve_events.jsonl"
        self.event_log.parent.mkdir(parents=True, exist_ok=True)
        self.metrics = AutoResolutionMetrics(metrics_log or self.audit_log.parent / "metrics.jsonl")
        self.divergence_threshold = divergence_threshold

        self._records: Dict[str, ResolutionRecord] = {}
        self._idempotency: Dict[str, ResolutionRecord] = {}
        self._versions: Dict[str, int] = {}

    # ---------------------------------------------------------------------
    # Public API
    # ---------------------------------------------------------------------
    def apply(self, **payload: Any) -> ResolutionRecord:
        """Apply a resolution using the unified Sprint 5 interface."""

        context = self._prepare_context(payload)

        idempotency_key = context["idempotency_key"]
        if idempotency_key:
            record = self._idempotency.get(idempotency_key)
            if record is not None:
                if record.event_id != context["event_id"]:
                    raise ResolutionError("Idempotency key reuse for different event")
                return record

        event_id = context["event_id"]
        provided_version = context["resource_version"]
        current_version = self._versions.get(event_id, 0)
        if provided_version != current_version:
            raise ResolutionConflictError(event_id, current_version, provided_version)

        record = (
            self._apply_legacy(context)
            if context["legacy_truth"] is not None
            else self._apply_modern(context)
        )

        self._records[event_id] = record
        self._versions[event_id] = current_version + 1
        if idempotency_key:
            self._idempotency[idempotency_key] = record

        self._write_audit(record, context)
        self._write_event(record, context)
        self._write_metrics(record, context)
        return record

    def load_audit_entries(self) -> List[Dict[str, Any]]:
        if not self.audit_log.exists():
            return []
        with self.audit_log.open("r", encoding="utf-8") as handle:
            return [json.loads(line) for line in handle if line.strip()]

    def load_metrics_entries(self) -> List[Dict[str, Any]]:
        if not self.metrics.metrics_log.exists():
            return []
        with self.metrics.metrics_log.open("r", encoding="utf-8") as handle:
            return [json.loads(line) for line in handle if line.strip()]

    def load_event_entries(self) -> List[Dict[str, Any]]:
        return self.load_decision_events()

    def load_decision_events(self) -> List[Dict[str, Any]]:
        if not self.event_log.exists():
            return []
        with self.event_log.open("r", encoding="utf-8") as handle:
            return [json.loads(line) for line in handle if line.strip()]

    # ------------------------------------------------------------------
    # Internal helpers
    # ------------------------------------------------------------------
    def _prepare_context(self, payload: Mapping[str, Any]) -> Dict[str, Any]:
        event_id = str(payload.get("event_id"))
        if not event_id:
            raise ValueError("event_id is required")

        actor = str(payload.get("actor", "").strip())
        role = str(payload.get("role", "").strip())
        if not actor:
            raise ValueError("actor is required")
        if not role:
            raise ValueError("role is required")
        if role not in ALLOWED_AUTO_ROLES:
            raise PermissionError(f"Role '{role}' not permitted to apply auto-resolution")

        resource_version = payload.get("resource_version")
        if resource_version is None:
            resource_version = self._versions.get(event_id, 0)
        try:
            resource_version = int(resource_version)
        except (TypeError, ValueError) as exc:
            expected = self._versions.get(event_id, 0)
            raise ResolutionConflictError(event_id, expected, resource_version) from exc

        idempotency_key = payload.get("idempotency_key")
        if idempotency_key is not None:
            idempotency_key = str(idempotency_key)
            if not idempotency_key:
                raise ValueError("idempotency_key cannot be empty")

        truth_source = payload.get("truth_source")
        if truth_source is not None and isinstance(truth_source, TruthSourceSignal):
            source_status = getattr(truth_source, "status", "pending")
            truth_source = truth_source.with_status(source_status)

        context = {
            "event_id": event_id,
            "actor": actor,
            "role": role,
            "resource_version": resource_version,
            "idempotency_key": idempotency_key,
            "trace_id": str(payload.get("trace_id") or uuid.uuid4().hex),
            "timestamp": payload.get("now") or time.time(),
            "quorum_votes": payload.get("quorum_votes"),
            "quorum": payload.get("quorum"),
            "truth_source": truth_source,
            "manual_override": payload.get("manual_override"),
            "manual_reason": payload.get("manual_reason"),
            "evidence_uri": payload.get("evidence_uri"),
            "manual_decision": payload.get("manual_decision"),
            "reason": payload.get("reason"),
            "legacy_truth": payload.get("truth"),
            "legacy_symbol": payload.get("symbol"),
            "metadata": payload.get("metadata"),
        }
        return context

    # ------------------------------------------------------------------
    # Legacy Sprint 4 interface
    # ------------------------------------------------------------------
    def _apply_legacy(self, ctx: Mapping[str, Any]) -> ResolutionRecord:
        truth: Mapping[str, Any] = ctx["legacy_truth"]
        quorum: Mapping[str, Any] = ctx["quorum"]
        if truth is None or quorum is None:
            raise ValueError("truth and quorum payloads are required for legacy apply")

        manual_decision = ctx["manual_decision"]
        result_reason = ctx["reason"]

        quorum_ok = bool(quorum.get("quorum_ok"))
        truth_value = truth.get("value")
        quorum_value = quorum.get("value")
        divergence = float(quorum.get("diverg_pct", 0.0))
        truth_rule_ok = False
        if truth_value is not None and quorum_value is not None:
            baseline = abs(truth_value) or 1.0
            delta = abs(quorum_value - truth_value) / baseline
            truth_rule_ok = delta <= self.divergence_threshold

        if manual_decision is not None:
            outcome_status = "applied_manual"
            manual_override = True
            final_decision = manual_decision
            rule = DecisionRule.MANUAL_OVERRIDE
            audit_action = "resolve.manual"
        elif quorum_ok and truth_rule_ok:
            outcome_status = "applied"
            manual_override = False
            final_decision = truth_value
            rule = DecisionRule.QUORUM_CONSENSUS
            audit_action = "resolve.auto"
        else:
            outcome_status = "manual_required"
            manual_override = False
            final_decision = None
            rule = DecisionRule.MANUAL_REVIEW
            audit_action = "resolve.manual_required"

        agreement_score = 1.0 if quorum_ok else 0.0
        decision_id = uuid.uuid4().hex
        record = ResolutionRecord(
            event_id=ctx["event_id"],
            decision_id=decision_id,
            outcome=_stringify_decision(final_decision),
            rule=rule,
            actor=ctx["actor"],
            role=ctx["role"],
            trace_id=ctx["trace_id"],
            decided_at=ctx["timestamp"],
            idempotency_key=ctx["idempotency_key"],
            resource_version=ctx["resource_version"] + 1,
            truth_source_used=False,
            manual_override=manual_override,
            quorum_ok=quorum_ok,
            agreement_score=agreement_score,
            truth_verdict=None,
            manual_reason=result_reason,
            evidence_uri=None,
            metadata={
                "symbol": ctx["legacy_symbol"],
                "truth": truth,
                "quorum": quorum,
                "truth_rule_ok": truth_rule_ok,
                "divergence_pct": divergence,
            },
            status=outcome_status,
        )
        record.metadata["audit_action"] = audit_action
        return record

    # ------------------------------------------------------------------
    # Modern Sprint 5 interface
    # ------------------------------------------------------------------
    def _apply_modern(self, ctx: Mapping[str, Any]) -> ResolutionRecord:
        started = time.perf_counter()
        quorum_votes = ctx["quorum_votes"]
        if quorum_votes is None:
            raise ValueError("quorum_votes is required")

        normalized_votes, agreement_score, majority_vote, quorum_ok, divergence = self._summarize_votes(
            quorum_votes
        )
        if not normalized_votes:
            raise ResolutionError("Quorum votes required to resolve event")

        manual_override = ctx["manual_override"]
        manual_reason = ctx["manual_reason"]
        evidence_uri = ctx["evidence_uri"]
        if manual_override is not None:
            if ctx["role"] not in ALLOWED_MANUAL_ROLES:
                raise PermissionError("Role not permitted to issue manual override")
            if not evidence_uri:
                raise ValueError("Manual override requires evidence_uri")

        truth_source: Optional[TruthSourceSignal] = ctx["truth_source"]
        if manual_override is not None:
            outcome = _stringify_decision(manual_override)
            rule = DecisionRule.MANUAL_OVERRIDE
            status = "applied_manual"
            truth_used = False
        elif truth_source is not None:
            truth_used, outcome, rule = self._resolve_with_truth(truth_source, majority_vote, quorum_ok)
            status = "applied"
        elif quorum_ok:
            outcome = _stringify_decision(majority_vote)
            rule = DecisionRule.QUORUM_CONSENSUS
            status = "applied"
            truth_used = False
        else:
            raise ResolutionError("Unable to resolve automatically; quorum requirement failed")

        decision_id = uuid.uuid4().hex
        extra_metadata: Dict[str, Any] = {}
        raw_metadata = ctx.get("metadata")
        if isinstance(raw_metadata, Mapping):
            extra_metadata = dict(raw_metadata)

        record = ResolutionRecord(
            event_id=ctx["event_id"],
            decision_id=decision_id,
            outcome=outcome,
            rule=rule,
            actor=ctx["actor"],
            role=ctx["role"],
            trace_id=ctx["trace_id"],
            decided_at=ctx["timestamp"],
            idempotency_key=ctx["idempotency_key"],
            resource_version=ctx["resource_version"] + 1,
            truth_source_used=truth_used,
            manual_override=manual_override is not None,
            quorum_ok=quorum_ok,
            agreement_score=agreement_score,
            truth_verdict=truth_source.verdict if truth_source else None,
            manual_reason=manual_reason,
            evidence_uri=evidence_uri,
            metadata={
                "quorum_votes": normalized_votes,
                "divergence_pct": divergence,
                "truth_source": truth_source.to_event_payload() if truth_source else None,
                "truth_rule_ok": truth_used or quorum_ok,
                "agreement_threshold": AGREEMENT_THRESHOLD,
                "metadata": extra_metadata if extra_metadata else None,
            },
            status=status,
        )
        duration_ms = (time.perf_counter() - started) * 1000
        telemetry.record_success(
            mode="modern",
            duration_ms=duration_ms,
            outcome=record.outcome or "unknown",
            truth_source_used=truth_used,
        )
        return record

    # ------------------------------------------------------------------
    def _resolve_with_truth(
        self,
        truth: TruthSourceSignal,
        majority_vote: Optional[str],
        quorum_ok: bool,
    ) -> Tuple[bool, str, str]:
        status = getattr(truth, "status", "pending").lower()
        if truth.verdict is None:
            if quorum_ok and majority_vote is not None:
                return False, _stringify_decision(majority_vote), DecisionRule.QUORUM_CONSENSUS
            raise ResolutionError("Truth source verdict missing and quorum not decisive")

        truth_decision = _stringify_decision(truth.verdict)
        truth_norm = _as_event_decision(truth_decision)
        truth_is_final = status in _FINAL_TRUTH_STATUSES
        if truth_is_final:
            majority_norm = None if majority_vote is None else _as_event_decision(_stringify_decision(majority_vote))
            if quorum_ok and majority_norm is not None and majority_norm != truth_norm:
                return True, truth_decision, DecisionRule.TRUTH_SOURCE_OVERRIDE
            return True, truth_decision, DecisionRule.TRUTH_SOURCE_FINAL

        if quorum_ok and majority_vote is not None:
            return False, _stringify_decision(majority_vote), DecisionRule.QUORUM_CONSENSUS
        raise ResolutionError("Truth source not final and quorum requirement failed")

    # ------------------------------------------------------------------
    def _summarize_votes(
        self, votes_payload: Any
    ) -> Tuple[List[str], float, Optional[str], bool, float]:
        if isinstance(votes_payload, Mapping):
            votes = votes_payload.get("votes", [])
            divergence = float(votes_payload.get("divergence_pct", 0.0))
        else:
            votes = votes_payload
            divergence = 0.0

        normalized: List[str] = []
        tally: Dict[str, float] = {}
        total_weight = 0.0
        if isinstance(votes, Mapping):
            iterator = votes.values()
        else:
            iterator = votes
        for vote in iterator or []:
            outcome, weight = _parse_vote(vote)
            normalized.append(outcome)
            tally[outcome] = tally.get(outcome, 0.0) + weight
            total_weight += weight

        if total_weight == 0:
            return normalized, 0.0, None, False, divergence

        majority_outcome = max(tally.items(), key=lambda item: item[1])[0]
        agreement_score = tally[majority_outcome] / total_weight
        quorum_ok = (
            bool(normalized)
            and divergence <= self.divergence_threshold
            and agreement_score >= AGREEMENT_THRESHOLD
        )
        return normalized, agreement_score, majority_outcome, quorum_ok, divergence

    # ------------------------------------------------------------------
    def _write_audit(self, record: ResolutionRecord, ctx: Mapping[str, Any]) -> None:
        payload = {
            "ts": _isoformat(record.decided_at),
            "event_id": record.event_id,
            "decision_id": record.decision_id,
            "actor": record.actor,
            "role": record.role,
            "trace_id": record.trace_id,
            "outcome": record.status,
            "decision": record.outcome,
            "rule": record.rule,
            "quorum_ok": record.quorum_ok,
            "truth_source_used": record.truth_source_used,
            "manual_override": record.manual_reason if record.manual_override and record.manual_reason else record.manual_override,
            "agreement_score": record.agreement_score,
            "resource_version": record.resource_version,
            "idempotency_key": record.idempotency_key,
            "quorum_votes": record.metadata.get("quorum_votes"),
            "truth_verdict": record.truth_verdict,
            "evidence_uri": record.evidence_uri,
        }
        if record.manual_reason is not None:
            payload["manual_override_reason"] = record.manual_reason
        if record.metadata.get("truth_source"):
            payload["truth_source"] = record.metadata["truth_source"]
        if record.metadata.get("metadata"):
            payload["metadata"] = record.metadata["metadata"]
        audit_action = record.metadata.get("audit_action")
        if not audit_action:
            if record.manual_override:
                audit_action = "resolve.manual"
            elif record.truth_source_used:
                audit_action = "resolve.truth"
            elif record.quorum_ok:
                audit_action = "resolve.auto"
            else:
                audit_action = "resolve.manual_required"
        payload["action"] = audit_action
        with self.audit_log.open("a", encoding="utf-8") as handle:
            handle.write(json.dumps(payload) + "\n")

    def _write_event(self, record: ResolutionRecord, ctx: Mapping[str, Any]) -> None:
        truth_source: Optional[TruthSourceSignal] = ctx["truth_source"]
        rule = _event_rule(record, truth_source)
        event = {
            "schema_version": RESOLVE_DECISION_SCHEMA_VERSION,
            "ts": _isoformat(record.decided_at),
            "event_id": record.event_id,
            "decision_id": record.decision_id,
            "rule": rule,
            "decision": _as_event_decision(record.outcome),
            "actor": record.actor,
            "role": record.role,
            "trace_id": record.trace_id,
            "manual_override": record.manual_override,
            "truth_source_used": record.truth_source_used,
            "quorum_ok": record.quorum_ok,
            "quorum_votes": record.metadata.get("quorum_votes"),
            "evidence_uri": record.evidence_uri,
            "idempotency_key": record.idempotency_key,
        }
        if record.manual_reason is not None:
            event["reason"] = record.manual_reason
        if truth_source:
            event["truth_source"] = truth_source.to_event_payload()
        with self.event_log.open("a", encoding="utf-8") as handle:
            handle.write(json.dumps(event) + "\n")

    def _write_metrics(self, record: ResolutionRecord, ctx: Mapping[str, Any]) -> None:
        duration = 0.0  # The service is synchronous; keep for compatibility.
        metrics_payload = {
            "ts": _isoformat(record.decided_at),
            "span": "auto_resolve.eval",
            "status": "success" if record.status != "manual_required" else "manual_required",
            "event_id": record.event_id,
            "trace_id": record.trace_id,
            "duration_ms": round(duration * 1000, 3),
            "outcome": record.outcome,
            "rule": record.rule,
            "truth_source_used": record.truth_source_used,
            "manual_override": record.manual_override,
            "quorum_ok": record.quorum_ok,
            "agreement_score": record.agreement_score,
            "agreement_threshold": AGREEMENT_THRESHOLD,
            "truth_rule_ok": record.metadata.get("truth_rule_ok", record.truth_source_used or record.quorum_ok),
        }
        self.metrics.emit(metrics_payload)


def _parse_vote(vote: Any) -> Tuple[str, float]:
    if isinstance(vote, Mapping):
        outcome = _normalize_vote(vote.get("verdict"))
        weight = float(vote.get("weight", 1.0))
    else:
        outcome = _normalize_vote(vote)
        weight = 1.0
    return outcome, max(weight, 0.0)


def _normalize_vote(value: Any) -> str:
    if value is None:
        return "rejected"
    lowered = str(value).strip().lower()
    if lowered in {"accepted", "accept", "yes", "y", "resolve_yes"}:
        return "accepted"
    if lowered in {"rejected", "reject", "no", "n", "resolve_no", "refund"}:
        return "rejected"
    return lowered or "rejected"


def _stringify_decision(value: Any) -> Optional[str]:
    if value is None:
        return None
    text = str(value).strip()
    return text


def _as_event_decision(outcome: Optional[str]) -> str:
    if outcome is None:
        return "rejected"
    lowered = outcome.lower()
    if lowered in {"accepted", "accept", "yes", "resolve_yes"}:
        return "accepted"
    if lowered in {"rejected", "reject", "no", "resolve_no", "refund"}:
        return "rejected"
    return "accepted"


def _event_rule(record: ResolutionRecord, truth: Optional[TruthSourceSignal]) -> str:
    if record.manual_override:
        return "manual.override"
    if truth and record.truth_source_used:
        safe_source = truth.source.lower().replace(" ", "_")
        return f"truth_source.{safe_source}"
    if record.quorum_ok:
        return "auto.quorum"
    return "manual.review"


def _isoformat(timestamp: float) -> str:
    return time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime(timestamp))


__all__ = [
    "AGREEMENT_THRESHOLD",
    "ALLOWED_AUTO_ROLES",
    "ALLOWED_MANUAL_ROLES",
    "AutoResolutionMetrics",
    "AutoResolutionService",
    "DecisionRule",
    "IdempotencyKeyConflict",
    "RESOLVE_DECISION_SCHEMA_VERSION",
    "ResolutionConflict",
    "ResolutionConflictError",
    "ResolutionError",
    "ResolutionRecord",
    "TruthSourceSignal",
]
