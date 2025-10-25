"""Auto-resolution service package."""
from .service import (
    AGREEMENT_THRESHOLD,
    ALLOWED_AUTO_ROLES,
    ALLOWED_MANUAL_ROLES,
    AutoResolutionMetrics,
    AutoResolutionService,
    ResolutionConflict,
    ResolutionError,
    ResolutionRecord,
    TruthSourceSignal,
)
from .api import apply_resolution

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
    "apply_resolution",
]
