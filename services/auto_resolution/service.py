"""Auto-resolution service combining quorum evaluation and truth-source overrides."""
from __future__ import annotations

from dataclasses import dataclass, asdict
from hashlib import sha256
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Sequence, TYPE_CHECKING
from typing import Dict, Iterable, List, Mapping, MutableMapping, Optional, Sequence, Tuple
import json
import time
import uuid

from .telemetry import telemetry as auto_resolution_telemetry

if TYPE_CHECKING:  # pragma: no cover - import used for typing only
    from .telemetry import AutoResolutionTelemetry

ALLOWED_AUTO_ROLES = {"resolver", "admin", "resolver_lead"}
ALLOWED_MANUAL_ROLES = {"admin", "resolver_lead"}
ALLOWED_AUTO_ROLES = {"operator", "admin"}
ALLOWED_MANUAL_ROLES = {"admin"}

DIVERGENCE_THRESHOLD = 0.01
AGREEMENT_THRESHOLD = 0.5

_AUTO_FAILURE_REASON = "no_resolution_path"


RESOLVE_DECISION_SCHEMA_VERSION = 1


class ResolutionError(RuntimeError):
    """Raised when a resolution cannot be applied automatically."""


class ResolutionConflict(ResolutionError):
    """Raised when `resource_version` semantics detect a conflict."""

    def __init__(self, message: str, *, resource_version: int) -> None:
        super().__init__(message)
        self.resource_version = resource_version


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
    resource_version: int
    agreement_score: float


class AutoResolutionMetrics:
    """Persist metrics/traces for auto-resolution evaluations."""

    def __init__(self, metrics_log: Path) -> None:
        self.metrics_log = metrics_log
        self.metrics_log.parent.mkdir(parents=True, exist_ok=True)

    def emit(
        self,
        *,
        status: str,
        event_id: str,
        trace_id: str,
        duration_s: float,
        outcome: Optional[str] = None,
        reason: Optional[str] = None,
        truth_source_used: Optional[bool] = None,
        manual_override: Optional[bool] = None,
        agreement_score: Optional[float] = None,
        error: Optional[str] = None,
    ) -> None:
        payload = {
            "ts": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
            "span": "auto_resolve.eval",
            "status": status,
            "event_id": event_id,
            "trace_id": trace_id,
            "duration_ms": round(duration_s * 1000, 3),
            "outcome": outcome,
            "reason": reason,
            "truth_source_used": truth_source_used,
            "manual_override": manual_override,
            "agreement_score": agreement_score,
            "error": error,
        }
        with self.metrics_log.open("a", encoding="utf-8") as fh:
            fh.write(json.dumps(payload) + "\n")


class AutoResolutionService:
    """Evaluate quorum decisions with truth-source overrides and audit logging."""

    def __init__(
        self,
        *,
        audit_log: Path,
        metrics_log: Optional[Path] = None,
        quorum_threshold: float = 2 / 3,
        truth_confidence_threshold: float = 0.7,
        telemetry: "AutoResolutionTelemetry" | None = None,
        divergence_threshold: float = DIVERGENCE_THRESHOLD,
    ) -> None:
        self.audit_log = audit_log
        self.audit_log.parent.mkdir(parents=True, exist_ok=True)
        self.decision_log = self.audit_log.parent / "resolve_decisions.jsonl"
        metrics_path = metrics_log or audit_log.parent / "metrics.jsonl"
        self.metrics = AutoResolutionMetrics(metrics_path)
        self.quorum_threshold = quorum_threshold
        self.truth_confidence_threshold = truth_confidence_threshold
        self.divergence_threshold = divergence_threshold
        self._idempotency: Dict[str, ResolutionRecord] = {}
        self._telemetry = telemetry or auto_resolution_telemetry
        self._backlog_events: Dict[str, str] = {}
        self._versions: Dict[str, int] = {}

    def apply(
        self,
        *,
        event_id: str,
        quorum_votes: Sequence[Mapping[str, object]] | Mapping[str, object] | Sequence[str],
        actor: str,
        role: str,
        idempotency_key: str,
        trace_id: Optional[str] = None,
        truth_source: Optional[TruthSourceSignal] = None,
        manual_override: Optional[str] = None,
        manual_reason: Optional[str] = None,
        evidence_uri: Optional[str] = None,
        resource_version: Optional[int] = None,
    ) -> ResolutionRecord:
        start = time.perf_counter()
        resolved_trace = trace_id or uuid.uuid4().hex
        self._require_idempotency_key(idempotency_key)
        existing = self._idempotency.get(idempotency_key)
        if existing is not None:
            if existing.event_id != event_id:
                raise ResolutionError("Idempotency key reuse for different event is not allowed")
            return existing

        current_version = self._versions.get(event_id, 0)
        if event_id in self._versions:
            if resource_version is None:
                raise ResolutionConflict(
                    "resource_version required for existing events",
                    resource_version=current_version,
                )
            if resource_version != current_version:
                raise ResolutionConflict(
                    "resource_version mismatch",
                    resource_version=current_version,
                )
        else:
            if resource_version not in (None, 0):
                raise ResolutionConflict(
                    "resource_version must be 0 for new events",
                    resource_version=0,
                )

        self._enforce_role(role, ALLOWED_AUTO_ROLES, action="apply resolution")

        start = time.perf_counter()
        mode = "manual" if manual_override is not None else "auto"
        span_attributes = {
            "auto_resolve.event_id": event_id,
            "auto_resolve.mode": mode,
            "auto_resolve.actor": actor,
            "auto_resolve.role": role,
        }
        if truth_source is not None:
            span_attributes["auto_resolve.truth_source"] = truth_source.source

        with self._telemetry.span("auto_resolve.apply", attributes=span_attributes) as span:
            try:
                if manual_override is not None:
                    self._enforce_role(role, ALLOWED_MANUAL_ROLES, action="perform manual override")
                    outcome, truth_used, reason = self._apply_manual_override(
                        manual_override, manual_reason
                    )
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
                self._clear_backlog(event_id)

                duration_ms = (time.perf_counter() - start) * 1000.0
                self._telemetry.record_success(
                    mode="manual" if manual_flag else "auto",
                    duration_ms=duration_ms,
                    outcome=record.outcome,
                    truth_source_used=record.truth_source_used,
                )

                if span is not None:
                    span.set_attribute("auto_resolve.outcome", record.outcome)
                    span.set_attribute("auto_resolve.truth_source_used", record.truth_source_used)
                    span.set_attribute("auto_resolve.quorum_ok", record.quorum_ok)
                    span.set_attribute("auto_resolve.manual_override", record.manual_override)

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
            except ResolutionError as exc:
                duration_ms = (time.perf_counter() - start) * 1000.0
                self._mark_backlog(event_id, _AUTO_FAILURE_REASON)
                self._telemetry.record_failure(
                    mode="auto",
                    duration_ms=duration_ms,
                    reason=_AUTO_FAILURE_REASON,
                )
                if span is not None:
                    self._telemetry.span_record_error(span, exc)
                raise
        votes, divergence = self._normalize_votes(quorum_votes)

        try:
            if manual_override is not None:
                record = self._apply_manual_override(
                    event_id=event_id,
                    votes=votes,
                    manual_override=manual_override,
                    manual_reason=manual_reason,
                    evidence_uri=evidence_uri,
                    resolved_trace=resolved_trace,
                    idempotency_key=idempotency_key,
                    role=role,
                    duration_start=start,
                    current_version=current_version,
                )
            else:
                record = self._apply_auto_logic(
                    event_id=event_id,
                    votes=votes,
                    divergence=divergence,
                    truth_source=truth_source,
                    resolved_trace=resolved_trace,
                    idempotency_key=idempotency_key,
                    duration_start=start,
                    current_version=current_version,
                )
        except Exception as exc:  # noqa: BLE001 - propagate after logging metrics
            duration = time.perf_counter() - start
            self.metrics.emit(
                status="error",
                event_id=event_id,
                trace_id=resolved_trace,
                duration_s=duration,
                error=str(exc),
            )
            raise

        self._idempotency[idempotency_key] = record
        self._versions[event_id] = record.resource_version
        self._append_audit(
            actor=actor,
            role=role,
            record=record,
            votes=votes,
            truth_source=truth_source,
            manual_reason=manual_reason,
            evidence_uri=evidence_uri,
        )
        return record

    def _apply_manual_override(
        self,
        *,
        event_id: str,
        votes: Sequence[Mapping[str, object]],
        manual_override: str,
        manual_reason: Optional[str],
        evidence_uri: Optional[str],
        resolved_trace: str,
        idempotency_key: str,
        role: str,
        duration_start: float,
        current_version: int,
    ) -> ResolutionRecord:
        self._enforce_role(role, ALLOWED_MANUAL_ROLES, action="perform manual override")
        if not evidence_uri:
            raise ValueError("Manual override requires evidence_uri")

        normalized = manual_override.lower()
        if normalized not in {"accepted", "rejected"}:
            raise ValueError("Manual override must be 'accepted' or 'rejected'")

        reason = manual_reason or "manual_override"
        record = self._finalize_record(
            event_id=event_id,
            outcome=normalized,
            reason=reason,
            resolved_trace=resolved_trace,
            idempotency_key=idempotency_key,
            quorum_ok=self._quorum_reached(votes),
            truth_source_used=False,
            manual_override=True,
            agreement_score=self._agreement_score(votes, normalized),
            current_version=current_version,
        )
        duration = time.perf_counter() - duration_start
        self.metrics.emit(
            status="success",
            event_id=event_id,
            trace_id=resolved_trace,
            duration_s=duration,
            outcome=record.outcome,
            reason=record.reason,
            truth_source_used=record.truth_source_used,
            manual_override=True,
            agreement_score=record.agreement_score,
        )
        return record

    def _apply_auto_logic(
        self,
        *,
        event_id: str,
        votes: Sequence[Mapping[str, object]],
        divergence: Optional[float],
        truth_source: Optional[TruthSourceSignal],
        resolved_trace: str,
        idempotency_key: str,
        duration_start: float,
        current_version: int,
    ) -> ResolutionRecord:
        if not votes:
            raise ResolutionError("Quorum votes required for auto resolution")

        quorum_ok = self._quorum_reached(votes)
        divergence_ok = divergence is None or divergence <= self.divergence_threshold
        majority_outcome = self._majority_outcome(votes)

        truth_used = False
        reason = "quorum"
        agreement = 0.0

        if truth_source and truth_source.confidence >= self.truth_confidence_threshold:
            agreement = self._agreement_score(votes, truth_source.verdict)
            truth_rule_ok = agreement >= AGREEMENT_THRESHOLD
            if truth_rule_ok or not quorum_ok or not divergence_ok:
                truth_used = True
                reason = f"truth_source:{truth_source.source}"
                outcome = truth_source.verdict
            else:
                raise ResolutionError(
                    "Truth source disagrees with quorum; manual review required",
                )
        else:
            if not quorum_ok or not divergence_ok:
                raise ResolutionError(
                    "Quorum or divergence conditions not satisfied",
                )
            outcome = majority_outcome
            agreement = self._agreement_score(votes, outcome)

        record = self._finalize_record(
            event_id=event_id,
            outcome=outcome,
            reason=reason,
            resolved_trace=resolved_trace,
            idempotency_key=idempotency_key,
            quorum_ok=quorum_ok and divergence_ok,
            truth_source_used=truth_used,
            manual_override=False,
            agreement_score=agreement,
            current_version=current_version,
        )
        duration = time.perf_counter() - duration_start
        self.metrics.emit(
            status="success",
            event_id=event_id,
            trace_id=resolved_trace,
            duration_s=duration,
            outcome=record.outcome,
            reason=record.reason,
            truth_source_used=record.truth_source_used,
            manual_override=False,
            agreement_score=record.agreement_score,
        )
        return record

    def _finalize_record(
        self,
        *,
        event_id: str,
        outcome: str,
        reason: str,
        resolved_trace: str,
        idempotency_key: str,
        quorum_ok: bool,
        truth_source_used: bool,
        manual_override: bool,
        agreement_score: float,
        current_version: int,
    ) -> ResolutionRecord:
        decided_at = time.time()
        record = ResolutionRecord(
            event_id=event_id,
            outcome=outcome,
            reason=reason,
            trace_id=resolved_trace,
            decided_at=decided_at,
            idempotency_key=idempotency_key,
            quorum_ok=quorum_ok,
            truth_source_used=truth_source_used,
            manual_override=manual_override,
            resource_version=current_version + 1,
            agreement_score=round(agreement_score, 4),
        )
        return record

    def _append_audit(
        self,
        *,
        actor: str,
        role: str,
        record: ResolutionRecord,
        votes: Sequence[Mapping[str, object]],
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
        payload: MutableMapping[str, object] = {
            "event_id": record.event_id,
            "quorum_votes": [dict(vote) for vote in votes],
            "truth_source": asdict(truth_source) if truth_source else None,
            "outcome": record.outcome,
            "reason": record.reason,
            "manual_reason": manual_reason,
            "evidence_uri": evidence_uri,
            "idempotency_key": record.idempotency_key,
            "resource_version": record.resource_version,
        }
        payload_hash = sha256(json.dumps(payload, sort_keys=True, default=str).encode("utf-8")).hexdigest()
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
            "resource_version": record.resource_version,
        }
        with self.audit_log.open("a", encoding="utf-8") as fh:
            fh.write(json.dumps(entry) + "\n")

    def _normalize_votes(
        self, quorum_votes: Sequence[Mapping[str, object]] | Mapping[str, object] | Sequence[str]
    ) -> Tuple[List[Mapping[str, object]], Optional[float]]:
        divergence: Optional[float] = None
        votes_list: Sequence[object]

        if isinstance(quorum_votes, Mapping):
            divergence_raw = quorum_votes.get("divergence_pct")
            divergence = float(divergence_raw) if divergence_raw is not None else None
            votes_list = quorum_votes.get("votes", [])  # type: ignore[assignment]
        else:
            votes_list = quorum_votes

        normalized: List[Mapping[str, object]] = []
        for vote in votes_list:
            if isinstance(vote, str):
                normalized.append({"source": "unknown", "verdict": vote.lower(), "weight": 1.0})
            elif isinstance(vote, Mapping):
                verdict = str(vote.get("verdict", "")).lower()
                if verdict not in {"accepted", "rejected"}:
                    raise ValueError("Vote verdict must be 'accepted' or 'rejected'")
                weight_raw = vote.get("weight", 1.0)
                try:
                    weight = float(weight_raw)
                except (TypeError, ValueError) as exc:  # pragma: no cover - defensive
                    raise ValueError("Vote weight must be numeric") from exc
                normalized.append(
                    {
                        "source": vote.get("source", "unknown"),
                        "verdict": verdict,
                        "weight": weight if weight > 0 else 0.0,
                    }
                )
            else:
                raise ValueError("Unsupported vote entry type")

        return normalized, divergence

    def _quorum_reached(self, votes: Sequence[Mapping[str, object]]) -> bool:
        total_weight = sum(float(vote.get("weight", 0.0)) for vote in votes)
        if total_weight <= 0:
            return False
        support = sum(float(vote.get("weight", 0.0)) for vote in votes if vote.get("verdict") == "accepted")
        ratio = support / total_weight
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
    def _majority_outcome(self, votes: Sequence[Mapping[str, object]]) -> str:
        support = sum(float(vote.get("weight", 0.0)) for vote in votes if vote.get("verdict") == "accepted")
        total = sum(float(vote.get("weight", 0.0)) for vote in votes)
        reject_support = total - support
        return "accepted" if support >= reject_support else "rejected"

    def _agreement_score(self, votes: Sequence[Mapping[str, object]], verdict: str) -> float:
        total_weight = sum(float(vote.get("weight", 0.0)) for vote in votes)
        if total_weight <= 0:
            return 0.0
        aligned = sum(
            float(vote.get("weight", 0.0)) for vote in votes if vote.get("verdict") == verdict
        )
        return aligned / total_weight

    def _enforce_role(self, role: str, allowed: Iterable[str], *, action: str) -> None:
        if role not in allowed:
            raise PermissionError(f"Role '{role}' not permitted to {action}")

    def _require_idempotency_key(self, key: str) -> None:
        if not key or len(key) < 8:
            raise ValueError("idempotency_key must be at least 8 characters long")

    def _mark_backlog(self, event_id: str, reason: str) -> None:
        if event_id not in self._backlog_events:
            self._backlog_events[event_id] = reason
            self._telemetry.adjust_backlog(delta=1, reason=reason)

    def _clear_backlog(self, event_id: str) -> None:
        reason = self._backlog_events.pop(event_id, None)
        if reason is not None:
            self._telemetry.adjust_backlog(delta=-1, reason=reason)

    def load_audit_entries(self) -> List[Dict[str, object]]:
        if not self.audit_log.exists():
            return []
        with self.audit_log.open("r", encoding="utf-8") as fh:
            return [json.loads(line) for line in fh if line.strip()]

    def load_metrics_entries(self) -> List[Dict[str, object]]:
        metrics_path = self.metrics.metrics_log
        if not metrics_path.exists():
            return []
        with metrics_path.open("r", encoding="utf-8") as fh:
            return [json.loads(line) for line in fh if line.strip()]


__all__ = [
    "AGREEMENT_THRESHOLD",
    "ALLOWED_AUTO_ROLES",
    "ALLOWED_MANUAL_ROLES",
    "AutoResolutionMetrics",
    "AutoResolutionService",
    "ResolutionConflict",
    "ResolutionError",
    "ResolutionRecord",
    "TruthSourceSignal",
]
