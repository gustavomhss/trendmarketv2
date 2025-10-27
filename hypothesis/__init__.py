"""Local compatibility shim for the Hypothesis package."""

from __future__ import annotations

from hypx_local import HealthCheck, Phase, given, settings, strategies

__all__ = ["given", "settings", "HealthCheck", "Phase", "strategies"]
