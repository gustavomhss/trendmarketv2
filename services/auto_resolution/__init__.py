"""Auto-resolution service module."""
from .api import AutoResolutionAPI, InvalidRequest
from .resolver import (
    ALLOWED_RESOLUTION_ROLES,
    AutoResolutionDecision,
    AutoResolutionService,
    DecisionConflict,
    DecisionRule,
    IdempotencyKeyConflict,
    ManualOverride,
    QuorumEvaluation,
    TruthSourcePayload,
)

__all__ = [
    "ALLOWED_RESOLUTION_ROLES",
    "AutoResolutionAPI",
    "AutoResolutionDecision",
    "AutoResolutionService",
    "DecisionConflict",
    "DecisionRule",
    "IdempotencyKeyConflict",
    "InvalidRequest",
    "ManualOverride",
    "QuorumEvaluation",
    "TruthSourcePayload",
"""Auto-resolution service package."""
from .service import (
    ALLOWED_AUTO_ROLES,
    ALLOWED_MANUAL_ROLES,
    AutoResolutionService,
    ResolutionError,
    ResolutionRecord,
    TruthSourceSignal,
)
from .api import apply_resolution

__all__ = [
    "ALLOWED_AUTO_ROLES",
    "ALLOWED_MANUAL_ROLES",
    "AutoResolutionService",
    "ResolutionError",
    "ResolutionRecord",
    "TruthSourceSignal",
    "apply_resolution",
]
