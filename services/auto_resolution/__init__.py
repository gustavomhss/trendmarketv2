"""Auto-resolution service exports."""
from .service import AutoResolutionService, ResolutionConflictError, ResolutionDecision

__all__ = [
    "AutoResolutionService",
    "ResolutionConflictError",
    "ResolutionDecision",
]
