"""Public exports for the auto-resolution package."""

from __future__ import annotations

from pathlib import Path
from typing import Iterable, Optional

from .api import AutoResolutionAPI, InvalidRequest, apply_resolution
from .resolver import (
    ALLOWED_RESOLUTION_ROLES,
    AutoResolutionDecision,
    AutoResolutionService as _ResolverAutoResolutionService,
    DecisionConflict,
    DecisionRule,
    IdempotencyKeyConflict,
    ManualOverride,
    QuorumEvaluation,
    TruthSourcePayload,
)
from .service import (
    AGREEMENT_THRESHOLD,
    ALLOWED_AUTO_ROLES,
    ALLOWED_MANUAL_ROLES,
    AutoResolutionMetrics,
    AutoResolutionService as _EngineAutoResolutionService,
    RESOLVE_DECISION_SCHEMA_VERSION,
    ResolutionConflict,
    ResolutionConflictError,
    ResolutionError,
    ResolutionRecord,
    TruthSourceSignal,
)


class AutoResolutionService(_ResolverAutoResolutionService):
    """Composite service exposing both the resolver and metrics interfaces."""

    def __init__(
        self,
        *,
        audit_log: Path,
        event_log: Optional[Path] = None,
        metrics_log: Optional[Path] = None,
        allowed_roles: Optional[Iterable[str]] = None,
        divergence_threshold: float = 0.01,
    ) -> None:
        self._engine = _EngineAutoResolutionService(
            audit_log=audit_log,
            event_log=event_log,
            metrics_log=metrics_log,
            divergence_threshold=divergence_threshold,
        )
        super().__init__(audit_log=audit_log, allowed_roles=allowed_roles)

    # ------------------------------------------------------------------
    # Modern engine delegation
    # ------------------------------------------------------------------
    def apply(self, **payload: object) -> ResolutionRecord:
        return self._engine.apply(**payload)

    def load_audit_entries(self) -> list[dict[str, object]]:  # type: ignore[override]
        return self._engine.load_audit_entries()

    def load_metrics_entries(self) -> list[dict[str, object]]:
        return self._engine.load_metrics_entries()

    def load_event_entries(self) -> list[dict[str, object]]:
        return self._engine.load_event_entries()

    def load_decision_events(self) -> list[dict[str, object]]:
        return self._engine.load_decision_events()


__all__ = [
    "AGREEMENT_THRESHOLD",
    "ALLOWED_AUTO_ROLES",
    "ALLOWED_MANUAL_ROLES",
    "ALLOWED_RESOLUTION_ROLES",
    "AutoResolutionAPI",
    "AutoResolutionDecision",
    "AutoResolutionMetrics",
    "AutoResolutionService",
    "DecisionConflict",
    "DecisionRule",
    "IdempotencyKeyConflict",
    "InvalidRequest",
    "ManualOverride",
    "QuorumEvaluation",
    "RESOLVE_DECISION_SCHEMA_VERSION",
    "ResolutionConflict",
    "ResolutionConflictError",
    "ResolutionError",
    "ResolutionRecord",
    "TruthSourcePayload",
    "TruthSourceSignal",
    "apply_resolution",
]
