"""HTTP-style API wrapper for the auto-resolution service."""
from __future__ import annotations

from typing import Any, Dict, Iterable

from .service import AutoResolutionService


class InvalidRequest(ValueError):
    """Raised when an inbound request payload is invalid."""


_REQUIRED_FIELDS: Iterable[str] = (
    "event_id",
    "symbol",
    "truth",
    "quorum",
    "actor",
    "role",
)


class AutoResolutionAPI:
    """Thin validation layer delegating to :class:`AutoResolutionService`."""

    def __init__(self, service: AutoResolutionService) -> None:
        self._service = service

    def apply(self, payload: Dict[str, Any]) -> Dict[str, str]:
        if not isinstance(payload, dict):
            raise InvalidRequest("payload must be a JSON object")

        missing = [field for field in _REQUIRED_FIELDS if field not in payload]
        if missing:
            joined = ", ".join(sorted(missing))
            raise InvalidRequest(f"missing required fields: {joined}")

        truth = payload["truth"]
        quorum = payload["quorum"]
        if not isinstance(truth, dict):
            raise InvalidRequest("truth must be an object")
        if not isinstance(quorum, dict):
            raise InvalidRequest("quorum must be an object")

        response = self._service.apply(
            event_id=str(payload["event_id"]),
            symbol=str(payload["symbol"]),
            truth=truth,
            quorum=quorum,
            actor=str(payload["actor"]),
            role=str(payload["role"]),
            idempotency_key=payload.get("idempotency_key"),
            manual_decision=payload.get("manual_decision"),
            reason=payload.get("reason"),
            trace_id=payload.get("trace_id"),
            resource_version=payload.get("resource_version"),
        )
        return response


__all__ = ["AutoResolutionAPI", "InvalidRequest"]
