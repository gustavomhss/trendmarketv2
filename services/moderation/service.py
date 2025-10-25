"""Moderation service with pause/resume/appeal endpoints and audit trail."""
from __future__ import annotations

from dataclasses import dataclass
from hashlib import sha256
from pathlib import Path
from typing import Dict, Iterable, List, Optional
import json
import time
import uuid

ALLOWED_PAUSE_ROLES = {"moderator", "admin"}
ALLOWED_RESUME_ROLES = {"moderator", "admin"}
ALLOWED_APPEAL_ROLES = {"operator", "admin"}


@dataclass
class ModerationRecord:
    symbol: str
    status: str
    reason: Optional[str]
    updated_at: float
    trace_id: str


class ModerationService:
    """In-memory moderation service with persistent audit log."""

    def __init__(self, audit_log: Path) -> None:
        self.audit_log = audit_log
        self.audit_log.parent.mkdir(parents=True, exist_ok=True)
        self.state: Dict[str, ModerationRecord] = {}

    def pause(
        self,
        *,
        symbol: str,
        reason: str,
        actor: str,
        role: str,
        evidence_uri: Optional[str] = None,
        trace_id: Optional[str] = None,
    ) -> ModerationRecord:
        self._enforce_role(role, ALLOWED_PAUSE_ROLES, action="pause")
        resolved_trace = trace_id or uuid.uuid4().hex
        ts = time.time()

        record = ModerationRecord(
            symbol=symbol,
            status="paused",
            reason=reason,
            updated_at=ts,
            trace_id=resolved_trace,
        )
        self.state[symbol] = record

        payload = {
            "symbol": symbol,
            "reason": reason,
            "evidence_uri": evidence_uri,
            "action": "pause",
        }
        self._append_audit(actor, role, payload, resolved_trace, outcome="accepted")
        return record

    def resume(
        self,
        *,
        symbol: str,
        actor: str,
        role: str,
        trace_id: Optional[str] = None,
    ) -> ModerationRecord:
        self._enforce_role(role, ALLOWED_RESUME_ROLES, action="resume")
        resolved_trace = trace_id or uuid.uuid4().hex
        ts = time.time()

        record = ModerationRecord(
            symbol=symbol,
            status="active",
            reason=None,
            updated_at=ts,
            trace_id=resolved_trace,
        )
        self.state[symbol] = record
        payload = {"symbol": symbol, "action": "resume"}
        self._append_audit(actor, role, payload, resolved_trace, outcome="accepted")
        return record

    def appeal(
        self,
        *,
        symbol: str,
        actor: str,
        role: str,
        reason: str,
        evidence_uri: Optional[str] = None,
        trace_id: Optional[str] = None,
    ) -> Dict[str, str]:
        self._enforce_role(role, ALLOWED_APPEAL_ROLES, action="appeal")
        resolved_trace = trace_id or uuid.uuid4().hex
        payload = {
            "symbol": symbol,
            "reason": reason,
            "evidence_uri": evidence_uri,
            "action": "appeal",
        }
        self._append_audit(actor, role, payload, resolved_trace, outcome="submitted")
        return {"symbol": symbol, "status": "under_review", "trace_id": resolved_trace}

    def _append_audit(
        self,
        actor: str,
        role: str,
        payload: Dict[str, Optional[str]],
        trace_id: str,
        *,
        outcome: str,
    ) -> None:
        ts_iso = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
        payload_hash = sha256(json.dumps(payload, sort_keys=True).encode("utf-8")).hexdigest()
        entry = {
            "ts": ts_iso,
            "actor": actor,
            "role": role,
            "action": payload.get("action"),
            "target": payload.get("symbol"),
            "payload_hash": payload_hash,
            "trace_id": trace_id,
            "outcome": outcome,
        }
        with self.audit_log.open("a", encoding="utf-8") as fh:
            fh.write(json.dumps(entry) + "\n")

    def _enforce_role(self, role: str, allowed: Iterable[str], *, action: str) -> None:
        if role not in allowed:
            raise PermissionError(f"Role '{role}' not permitted to {action}")

    def load_audit_entries(self) -> List[Dict[str, object]]:
        if not self.audit_log.exists():
            return []
        with self.audit_log.open("r", encoding="utf-8") as fh:
            return [json.loads(line) for line in fh if line.strip()]


__all__ = ["ModerationService", "ModerationRecord"]


