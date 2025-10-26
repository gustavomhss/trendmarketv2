from __future__ import annotations

from dataclasses import dataclass
from hashlib import sha256
from pathlib import Path
from statistics import mean
from typing import Dict, Iterable, List, Optional
import json
import time
import uuid

from services.telemetry import TelemetryManager, TelemetrySettings

ALLOWED_PAUSE_ROLES = {"moderator", "admin"}
ALLOWED_RESUME_ROLES = {"moderator", "admin"}
ALLOWED_APPEAL_ROLES = {"operator", "admin", "system"}

_TELEMETRY = TelemetryManager(TelemetrySettings(service_name="moderation-service"))
_SPAN_APPLY = "moderation.apply"
_EVENT_LOG = _TELEMETRY.event_log(
    "MBP_MODERATION_EVENT_LOG",
    Path("out/moderation/events.jsonl"),
)
_MTTD_GAUGE = _TELEMETRY.gauge("mbp_moderation_mttd_seconds", "Mean time to detect moderation incidents")
_MTTM_GAUGE = _TELEMETRY.gauge("mbp_moderation_mttm_seconds", "Mean time to mitigate moderation incidents")
_APPEALS_COUNTER = _TELEMETRY.counter(
    "mbp_moderation_appeals_total",
    "Total moderation appeals emitted by the service.",
    labelnames=("type",),
)


@dataclass
class ModerationRecord:
    symbol: str
    status: str
    reason: Optional[str]
    updated_at: float
    trace_id: str
    evidence_uri: Optional[str] = None


class ModerationService:
    """In-memory moderation service with persistent audit log."""

    def __init__(self, audit_log: Path) -> None:
        self.audit_log = audit_log
        self.audit_log.parent.mkdir(parents=True, exist_ok=True)
        self.state: Dict[str, ModerationRecord] = {}
        self._pause_started_at: Dict[str, float] = {}
        self._mttd_samples: List[float] = []
        self._mttm_samples: List[float] = []
        self._appeals: List[Dict[str, object]] = []

    def pause(
        self,
        *,
        symbol: str,
        reason: str,
        actor: str,
        role: str,
        evidence_uri: Optional[str] = None,
        trace_id: Optional[str] = None,
        detected_at: Optional[float] = None,
        auto_appeal: bool = True,
    ) -> ModerationRecord:
        self._enforce_role(role, ALLOWED_PAUSE_ROLES, action="pause")
        if not evidence_uri:
            raise ValueError("pause action requires evidence_uri for auditability")
        resolved_trace = trace_id or uuid.uuid4().hex
        ts = time.time()

        if detected_at is not None:
            delta = max(0.0, ts - detected_at)
            self._mttd_samples.append(delta)
            _MTTD_GAUGE.set(mean(self._mttd_samples))

        record = ModerationRecord(
            symbol=symbol,
            status="paused",
            reason=reason,
            updated_at=ts,
            trace_id=resolved_trace,
            evidence_uri=evidence_uri,
        )
        self.state[symbol] = record
        self._pause_started_at[symbol] = ts

        payload = {
            "symbol": symbol,
            "reason": reason,
            "evidence_uri": evidence_uri,
            "action": "pause",
        }
        self._append_audit(actor, role, payload, resolved_trace, outcome="accepted")

        with _TELEMETRY.span(_SPAN_APPLY, attributes={"moderation.symbol": symbol, "moderation.action": "pause"}):
            _EVENT_LOG.emit(
                "moderation.pause",
                {
                    "symbol": symbol,
                    "reason": reason,
                    "actor": actor,
                    "role": role,
                    "evidence_uri": evidence_uri,
                    "trace_id": resolved_trace,
                },
            )

        if auto_appeal:
            self._auto_appeal(symbol=symbol, reason=reason, evidence_uri=evidence_uri)

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

        pause_ts = self._pause_started_at.pop(symbol, None)
        if pause_ts is not None:
            duration = max(0.0, ts - pause_ts)
            self._mttm_samples.append(duration)
            _MTTM_GAUGE.set(mean(self._mttm_samples))

        payload = {"symbol": symbol, "action": "resume"}
        self._append_audit(actor, role, payload, resolved_trace, outcome="accepted")

        with _TELEMETRY.span(_SPAN_APPLY, attributes={"moderation.symbol": symbol, "moderation.action": "resume"}):
            _EVENT_LOG.emit(
                "moderation.resume",
                {
                    "symbol": symbol,
                    "actor": actor,
                    "role": role,
                    "trace_id": resolved_trace,
                },
            )

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
        auto: bool = False,
    ) -> Dict[str, str]:
        self._enforce_role(role, ALLOWED_APPEAL_ROLES, action="appeal")
        resolved_trace = trace_id or uuid.uuid4().hex
        payload = {
            "symbol": symbol,
            "reason": reason,
            "evidence_uri": evidence_uri,
            "action": "appeal",
            "auto": auto,
        }
        self._append_audit(actor, role, payload, resolved_trace, outcome="submitted")

        self._appeals.append({
            "symbol": symbol,
            "reason": reason,
            "actor": actor,
            "role": role,
            "trace_id": resolved_trace,
            "auto": auto,
        })
        _APPEALS_COUNTER.labels(type="auto" if auto else "manual").inc()

        _EVENT_LOG.emit(
            "moderation.appeal",
            {
                "symbol": symbol,
                "reason": reason,
                "actor": actor,
                "role": role,
                "trace_id": resolved_trace,
                "auto": auto,
            },
        )
        return {"symbol": symbol, "status": "under_review", "trace_id": resolved_trace}

    def generate_ops_report(self, out_path: Path) -> Dict[str, object]:
        out_path.parent.mkdir(parents=True, exist_ok=True)
        report = {
            "generated_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
            "mttd_seconds": mean(self._mttd_samples) if self._mttd_samples else None,
            "mttm_seconds": mean(self._mttm_samples) if self._mttm_samples else None,
            "appeals_total": len(self._appeals),
            "appeals_auto": sum(1 for item in self._appeals if item.get("auto")),
            "active_pauses": [record.symbol for record in self.state.values() if record.status == "paused"],
            "evidence_uris": {record.symbol: record.evidence_uri for record in self.state.values() if record.evidence_uri},
        }
        out_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
        return report

    def _auto_appeal(self, *, symbol: str, reason: str, evidence_uri: Optional[str]) -> None:
        system_actor = "auto-appeal"
        try:
            self.appeal(
                symbol=symbol,
                actor=system_actor,
                role="system",
                reason=reason,
                evidence_uri=evidence_uri,
                auto=True,
            )
        except PermissionError:
            # system role should be allowed but keep defensive guard
            pass

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
