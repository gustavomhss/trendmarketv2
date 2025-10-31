from __future__ import annotations

import hashlib
from dataclasses import dataclass

# Curve constants derived from RFC 8032 / Bernstein et al reference implementation.
Q = 2**255 - 19
L = 2**252 + 27742317777372353535851937790883648493
D = (-121665 * pow(121666, Q - 2, Q)) % Q
I = pow(2, (Q - 1) // 4, Q)

# Base point coordinates
BASE_X = 15112221349535400772501151409588531511454012693041857206046113283949847762202 % Q
BASE_Y = 46316835694926478169428394003475163141307993866256225615783033603165251855960 % Q
BASE_POINT = (BASE_X, BASE_Y)


class BadSignatureError(Exception):
    """Raised when an Ed25519 signature fails verification."""


def _int_from_bytes(data: bytes) -> int:
    return int.from_bytes(data, "little")


def _int_to_bytes(value: int) -> bytes:
    return value.to_bytes(32, "little")


def _isoncurve(point: tuple[int, int]) -> bool:
    x, y = point
    return (-(x * x) + y * y - 1 - D * x * x * y * y) % Q == 0


def _xrecover(y: int) -> int:
    xx = (y * y - 1) % Q
    denom = (D * y * y + 1) % Q
    inv_denom = pow(denom, Q - 2, Q)
    xx = (xx * inv_denom) % Q
    x = pow(xx, (Q + 3) // 8, Q)
    if (x * x - xx) % Q != 0:
        x = (x * I) % Q
    if x % 2 != 0:
        x = Q - x
    return x


def _decodepoint(data: bytes) -> tuple[int, int]:
    if len(data) != 32:
        raise ValueError("Ed25519 public keys must be 32 bytes")
    y = _int_from_bytes(data) % (1 << 255)
    x = _xrecover(y)
    if (x & 1) != (data[31] >> 7):
        x = Q - x
    point = (x, y)
    if not _isoncurve(point):
        raise ValueError("Decoded point is not on curve")
    return point


def _encodepoint(point: tuple[int, int]) -> bytes:
    x, y = point
    data = bytearray(_int_to_bytes(y))
    data[31] |= (x & 1) << 7
    return bytes(data)


def _edwards_add(p: tuple[int, int], q: tuple[int, int]) -> tuple[int, int]:
    (x1, y1) = p
    (x2, y2) = q
    denominator = (1 + D * x1 * x2 * y1 * y2) % Q
    inv_denom = pow(denominator, Q - 2, Q)
    x3 = ((x1 * y2 + x2 * y1) * inv_denom) % Q
    denominator2 = (1 - D * x1 * x2 * y1 * y2) % Q
    inv_denom2 = pow(denominator2, Q - 2, Q)
    y3 = ((y1 * y2 + x1 * x2) * inv_denom2) % Q
    return (x3, y3)


def _scalarmult(point: tuple[int, int], scalar: int) -> tuple[int, int]:
    result = (0, 1)
    addend = point
    k = scalar
    while k > 0:
        if k & 1:
            result = _edwards_add(result, addend)
        addend = _edwards_add(addend, addend)
        k >>= 1
    return result


def _clamp_scalar(secret: bytes) -> tuple[int, bytes]:
    if len(secret) != 32:
        raise ValueError("Seed must be 32 bytes")
    h = bytearray(hashlib.sha512(secret).digest())
    h[0] &= 248
    h[31] &= 63
    h[31] |= 64
    scalar = _int_from_bytes(bytes(h[:32]))
    prefix = bytes(h[32:])
    return scalar, prefix


def _public_from_scalar(scalar: int) -> bytes:
    point = _scalarmult(BASE_POINT, scalar)
    return _encodepoint(point)


def _hash(data: bytes) -> int:
    return _int_from_bytes(hashlib.sha512(data).digest())


def _signature(message: bytes, secret: bytes, public_key: bytes) -> bytes:
    scalar, prefix = _clamp_scalar(secret)
    r = (_hash(prefix + message) % L)
    r_point = _scalarmult(BASE_POINT, r)
    r_encoded = _encodepoint(r_point)
    h = _hash(r_encoded + public_key + message) % L
    s = (r + h * scalar) % L
    return r_encoded + _int_to_bytes(s)


def _check_signature(message: bytes, signature: bytes, public_key: bytes) -> bool:
    if len(signature) != 64:
        return False
    r_encoded = signature[:32]
    s = _int_from_bytes(signature[32:])
    if s >= L:
        return False
    try:
        a_point = _decodepoint(public_key)
        r_point = _decodepoint(r_encoded)
    except ValueError:
        return False
    h = _hash(r_encoded + public_key + message) % L
    s_b = _scalarmult(BASE_POINT, s)
    r_plus_ah = _edwards_add(r_point, _scalarmult(a_point, h))
    return _encodepoint(r_plus_ah) == _encodepoint(s_b)


@dataclass(frozen=True)
class VerifyKey:
    key: bytes

    def __post_init__(self) -> None:
        if len(self.key) != 32:
            raise ValueError("Ed25519 public keys must be 32 bytes")
        # Validate key decodes correctly
        _decodepoint(self.key)

    def verify(self, message: bytes, signature: bytes) -> None:
        if not _check_signature(message, signature, self.key):
            raise BadSignatureError("invalid Ed25519 signature")

    def __bytes__(self) -> bytes:
        return self.key

    def to_bytes(self) -> bytes:
        return self.key


class SigningKey:
    def __init__(self, seed: bytes) -> None:
        if len(seed) != 32:
            raise ValueError("Ed25519 seeds must be 32 bytes")
        self._seed = seed
        scalar, _ = _clamp_scalar(seed)
        self._public_key = _public_from_scalar(scalar)

    @property
    def verify_key(self) -> VerifyKey:
        return VerifyKey(self._public_key)

    def sign(self, message: bytes) -> bytes:
        return _signature(message, self._seed, self._public_key)
