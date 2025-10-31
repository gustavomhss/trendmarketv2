"""Minimalistic SigningKey/VerifyKey implementation."""
from __future__ import annotations

import hashlib
from dataclasses import dataclass

from .exceptions import BadSignatureError


class SignedMessage(bytes):
    """Container mimicking PyNaCl's SignedMessage."""

    def __new__(cls, signature: bytes) -> "SignedMessage":
        return bytes.__new__(cls, signature)

    @property
    def signature(self) -> bytes:
        return bytes(self)


@dataclass
class VerifyKey:
    _key: bytes

    def __post_init__(self) -> None:
        if not isinstance(self._key, (bytes, bytearray)) or len(self._key) != 32:
            raise ValueError("VerifyKey expects 32 raw bytes")
        self._key = bytes(self._key)

    def __bytes__(self) -> bytes:  # pragma: no cover - trivial
        return self._key

    def verify(self, message: bytes, signature: bytes) -> bytes:
        expected = _signature_for(self._key, message)
        if signature != expected:
            raise BadSignatureError("Signature verification failed")
        return message


class SigningKey:
    def __init__(self, seed: bytes):
        if not isinstance(seed, (bytes, bytearray)) or len(seed) != 32:
            raise ValueError("SigningKey seed must be 32 bytes")
        self._seed = bytes(seed)
        self.verify_key = VerifyKey(_public_from_seed(self._seed))

    def sign(self, message: bytes) -> SignedMessage:
        if not isinstance(message, (bytes, bytearray)):
            raise TypeError("message must be bytes-like")
        signature = _signature_for(bytes(self.verify_key), bytes(message))
        return SignedMessage(signature)


def _public_from_seed(seed: bytes) -> bytes:
    return hashlib.sha256(seed).digest()


def _signature_for(public_key: bytes, message: bytes) -> bytes:
    first = hashlib.sha256(public_key + message).digest()
    second = hashlib.sha256(message + public_key).digest()
    return first + second


__all__ = ["SigningKey", "VerifyKey", "SignedMessage"]
