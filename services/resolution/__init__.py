"""Auto-resolution service package."""

from .service import (
    AutoResolverService,
    DecisionConflictError,
    ResolutionRecord,
    PendingDecision,
)

__all__ = [
    "AutoResolverService",
    "DecisionConflictError",
    "PendingDecision",
    "ResolutionRecord",
]
