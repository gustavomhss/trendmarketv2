"""Auto-resolution service combining truth-source inputs and quorum outcomes."""
from __future__ import annotations

from dataclasses import dataclass
from hashlib import sha256
from pathlib import Path
from typing import Dict, Optional, Any, List
import json
import time
import uuid

MANUAL_ROLES = {"operator", "admin"}


class ResolutionConflictError(RuntimeError):
    """Raised when attempting to apply a decision with a stale resource version."""


@dataclass
class ResolutionDecision:
    event_id: str
    decision_id: str
    rule: str
    decision: Optional[str]
    outcome: str
    actor: str
    role: str
    trace_id: str
    decided_at: float
    resource_version: str
    manual: bool
    metadata: Dict[str, Any]

    def to_response(self) -> Dict[str, str]:
        return {
            "decision_id": self.decision_id,
            "outcome": self.outcome,
            "rule": self.rule,
            "trace_id": self.trace_id,
            "resource_version": self.resource_version,
        }


class AutoResolutionService:
    """Evaluates quorum decisions against a truth source with auditability."""

    def __init__(
        self,
        *,
        audit_log: Path,
        event_log: Path,
        metrics_log: Path,
        tolerance_pct: float = 0.01,
    ) -> None:
        self.audit_log = audit_log
        self.event_log = event_log
        self.metrics_log = metrics_log
        for log in (self.audit_log, self.event_log, self.metrics_log):
            log.parent.mkdir(parents=True, exist_ok=True)
        self.tolerance_pct = tolerance_pct
        self.decisions: Dict[str, ResolutionDecision] = {}
        self.idempotency: Dict[str, str] = {}
        self._version_counter = 0

    def apply(
        self,
        *,
        event_id: str,
        symbol: str,
        truth: Dict[str, Any],
        quorum: Dict[str, Any],
        actor: str,
        role: str,
        idempotency_key: Optional[str] = None,
        manual_decision: Optional[str] = None,
        reason: Optional[str] = None,
        trace_id: Optional[str] = None,
        resource_version: Optional[str] = None,
        now: Optional[float] = None,
    ) -> Dict[str, str]:
        """Apply an auto-resolution decision ensuring RBAC, idempotency, and auditing."""

        if idempotency_key and idempotency_key in self.idempotency:
            stored_event_id = self.idempotency[idempotency_key]
            return self.decisions[stored_event_id].to_response()

        existing = self.decisions.get(event_id)
        if existing:
            if resource_version and resource_version != existing.resource_version:
                raise ResolutionConflictError(
                    f"Event {event_id} already decided with version {existing.resource_version}"
                )
            return existing.to_response()

        decided_at = now if now is not None else time.time()
        trace = trace_id or uuid.uuid4().hex
        outcome = "applied"
        manual = False
        decision_value: Optional[str] = None
        metadata: Dict[str, Any] = {
            "symbol": symbol,
            "truth": truth,
            "quorum": quorum,
        }

        if manual_decision is not None:
            self._enforce_manual_role(role)
            decision_value = manual_decision
            rule = "MANUAL_OVERRIDE"
            outcome = "applied_manual"
            manual = True
            if reason:
                metadata["reason"] = reason
        else:
            evaluation = self._evaluate_truth(truth, quorum)
            metadata["evaluation"] = evaluation
            rule = evaluation["rule"]
            if not evaluation["quorum_ok"] or not evaluation["truth_rule_ok"]:
                outcome = "manual_required"
                decision_value = evaluation.get("proposed_decision")
            else:
                decision_value = evaluation["proposed_decision"]

        decision_id = uuid.uuid4().hex
        self._version_counter += 1
        resource_ver = resource_version or f"v{self._version_counter:04d}"
        record = ResolutionDecision(
            event_id=event_id,
            decision_id=decision_id,
            rule=rule,
            decision=decision_value,
            outcome=outcome,
            actor=actor,
            role=role,
            trace_id=trace,
            decided_at=decided_at,
            resource_version=resource_ver,
            manual=manual,
            metadata=metadata,
        )
        self.decisions[event_id] = record
        if idempotency_key:
            self.idempotency[idempotency_key] = event_id

        payload = {
            "event_id": event_id,
            "decision": decision_value,
            "rule": rule,
            "outcome": outcome,
            "reason": reason,
            "manual": manual,
        }
        self._append_audit(actor, role, payload, trace, decided_at)
        self._append_event(record)
        self._append_metrics(record)
        return record.to_response()

    def get_decision(self, event_id: str) -> Optional[ResolutionDecision]:
        return self.decisions.get(event_id)

    def load_audit_entries(self) -> List[Dict[str, Any]]:
        if not self.audit_log.exists():
            return []
        with self.audit_log.open("r", encoding="utf-8") as fh:
            return [json.loads(line) for line in fh if line.strip()]

    def load_event_entries(self) -> List[Dict[str, Any]]:
        if not self.event_log.exists():
            return []
        with self.event_log.open("r", encoding="utf-8") as fh:
            return [json.loads(line) for line in fh if line.strip()]

    def load_metrics_entries(self) -> List[Dict[str, Any]]:
        if not self.metrics_log.exists():
            return []
        with self.metrics_log.open("r", encoding="utf-8") as fh:
            return [json.loads(line) for line in fh if line.strip()]

    def _evaluate_truth(self, truth: Dict[str, Any], quorum: Dict[str, Any]) -> Dict[str, Any]:
        truth_value = truth.get("value")
        truth_source = truth.get("source")
        truth_ts = truth.get("ts")
        quorum_ok = bool(quorum.get("quorum_ok"))
        quorum_value = quorum.get("value")
        staleness_ms = quorum.get("staleness_ms", 0)
        divergence = quorum.get("diverg_pct")
        proposed_decision = None
        rule = "AUTO_TRUTH_MATCH"
        truth_rule_ok = False

        if truth_value is not None and quorum_value is not None:
            baseline = abs(truth_value) if abs(truth_value) > 1e-9 else 1.0
            delta_pct = abs(quorum_value - truth_value) / baseline
            truth_rule_ok = delta_pct <= self.tolerance_pct
            proposed_decision = str(truth_value)
        else:
            delta_pct = None
            rule = "TRUTH_SOURCE_MISSING"

        if divergence is not None and divergence > self.tolerance_pct:
            truth_rule_ok = False
            rule = "DIVERGENCE_THRESHOLD"
        elif staleness_ms and staleness_ms > 30000:
            truth_rule_ok = False
            rule = "STALENESS_THRESHOLD"
        elif not quorum_ok:
            rule = "QUORUM_INSUFFICIENT"
        elif truth_rule_ok:
            rule = "AUTO_TRUTH_MATCH"

        return {
            "truth_source": truth_source,
            "truth_ts": truth_ts,
            "quorum_ok": quorum_ok,
            "truth_rule_ok": truth_rule_ok,
            "delta_pct": delta_pct,
            "rule": rule,
            "proposed_decision": proposed_decision,
        }

    def _enforce_manual_role(self, role: str) -> None:
        if role not in MANUAL_ROLES:
            raise PermissionError(f"Role '{role}' cannot perform manual override")

    def _append_audit(
        self,
        actor: str,
        role: str,
        payload: Dict[str, Any],
        trace_id: str,
        decided_at: float,
    ) -> None:
        ts_iso = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime(decided_at))
        payload_hash = sha256(json.dumps(payload, sort_keys=True).encode("utf-8")).hexdigest()
        entry = {
            "ts": ts_iso,
            "actor": actor,
            "role": role,
            "action": "resolve.manual" if payload.get("manual") else "resolve.auto",
            "target": payload.get("event_id"),
            "payload_hash": payload_hash,
            "trace_id": trace_id,
            "outcome": payload.get("outcome"),
        }
        with self.audit_log.open("a", encoding="utf-8") as fh:
            fh.write(json.dumps(entry) + "\n")

    def _append_event(self, record: ResolutionDecision) -> None:
        event_entry = {
            "schema_version": 1,
            "ts": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime(record.decided_at)),
            "event_id": record.event_id,
            "decision_id": record.decision_id,
            "rule": record.rule,
            "decision": record.decision,
            "actor": record.actor,
            "role": record.role,
            "outcome": record.outcome,
            "trace_id": record.trace_id,
            "metadata": record.metadata,
        }
        with self.event_log.open("a", encoding="utf-8") as fh:
            fh.write(json.dumps(event_entry) + "\n")

    def _append_metrics(self, record: ResolutionDecision) -> None:
        evaluation = record.metadata.get("evaluation", {})
        truth_ts = record.metadata.get("truth", {}).get("ts")
        latency_ms: Optional[float]
        if isinstance(truth_ts, (int, float)):
            latency_ms = max(0.0, (record.decided_at - float(truth_ts)) * 1000)
        else:
            latency_ms = None
        metric_entry = {
            "ts": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime(record.decided_at)),
            "event_id": record.event_id,
            "decision_id": record.decision_id,
            "outcome": record.outcome,
            "rule": record.rule,
            "quorum_ok": bool(record.metadata.get("quorum", {}).get("quorum_ok")),
            "truth_rule_ok": evaluation.get("truth_rule_ok") if evaluation else None,
            "latency_ms": latency_ms,
            "manual": record.manual,
        }
        with self.metrics_log.open("a", encoding="utf-8") as fh:
            fh.write(json.dumps(metric_entry) + "\n")


__all__ = [
    "AutoResolutionService",
    "ResolutionConflictError",
    "ResolutionDecision",
]
