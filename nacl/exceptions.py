"""Exceptions compatible with the subset of PyNaCl used in tests."""
from __future__ import annotations


class BadSignatureError(Exception):
    """Raised when signature verification fails."""


__all__ = ["BadSignatureError"]
