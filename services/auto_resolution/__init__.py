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
]
