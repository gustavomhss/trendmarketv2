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
