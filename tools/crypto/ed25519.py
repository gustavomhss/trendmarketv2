"""Pure-Python Ed25519 helpers based on the public-domain reference implementation."""
from __future__ import annotations

import hashlib
from typing import Tuple

b = 256
q = 2**255 - 19
L_ORDER = 2**252 + 27742317777372353535851937790883648493

d = -121665 * pow(121666, q - 2, q) % q
SQRT_MINUS_ONE = pow(2, (q - 1) // 4, q)

B_x = 15112221349535400772501151409588531511454012693041857206046113283949847762202
B_y = 46316835694926478169428394003475163141307993866256225615783033603165251855960
B = (B_x % q, B_y % q)


def _H(m: bytes) -> bytes:
    return hashlib.sha512(m).digest()


def _expmod(base: int, exp: int, mod: int) -> int:
    if exp == 0:
        return 1
    t = _expmod(base, exp // 2, mod) ** 2 % mod
    if exp & 1:
        t = (t * base) % mod
    return t


def _inv(x: int) -> int:
    return pow(x, q - 2, q)


def _xrecover(y: int) -> int:
    xx = (y * y - 1) * _inv(d * y * y + 1)
    x = _expmod(xx, (q + 3) // 8, q)
    if (x * x - xx) % q != 0:
        x = (x * SQRT_MINUS_ONE) % q
    if x % 2 != 0:
        x = q - x
    return x


def _edwards_add(P: Tuple[int, int], Q: Tuple[int, int]) -> Tuple[int, int]:
    (x1, y1) = P
    (x2, y2) = Q
    denom_x = _inv(1 + d * x1 * x2 * y1 * y2)
    denom_y = _inv(1 - d * x1 * x2 * y1 * y2)
    x3 = (x1 * y2 + x2 * y1) * denom_x % q
    y3 = (y1 * y2 + x1 * x2) * denom_y % q
    return x3, y3


def _scalarmult(P: Tuple[int, int], e: int) -> Tuple[int, int]:
    if e == 0:
        return 0, 1
    Q = _scalarmult(P, e // 2)
    Q = _edwards_add(Q, Q)
    if e & 1:
        Q = _edwards_add(Q, P)
    return Q


def _encodepoint(P: Tuple[int, int]) -> bytes:
    (x, y) = P
    bits = y.to_bytes(32, "little")
    bits = bytearray(bits)
    bits[-1] = (bits[-1] & 0x7F) | ((x & 1) << 7)
    return bytes(bits)


def _decodepoint(s: bytes) -> Tuple[int, int]:
    if len(s) != 32:
        raise ValueError("Invalid encoded point length")
    y = int.from_bytes(s, "little") & ((1 << 255) - 1)
    sign = s[31] >> 7
    x = _xrecover(y)
    if (x & 1) != sign:
        x = q - x
    P = (x, y)
    if not _isoncurve(P):
        raise ValueError("Point not on curve")
    return P


def _isoncurve(P: Tuple[int, int]) -> bool:
    x, y = P
    return (-x * x + y * y - 1 - d * x * x * y * y) % q == 0


def _encodeint(n: int) -> bytes:
    return n.to_bytes(32, "little")


def _decodeint(s: bytes) -> int:
    return int.from_bytes(s, "little")


def _clamp_scalar(h: bytes) -> int:
    a = int.from_bytes(h[:32], "little")
    a &= (1 << 254) - 8
    a |= 1 << 254
    return a


def public_key(seed: bytes) -> bytes:
    if len(seed) != 32:
        raise ValueError("Seed must be 32 bytes")
    h = _H(seed)
    a = _clamp_scalar(h)
    return _encodepoint(_scalarmult(B, a))


def sign(message: bytes, seed: bytes, public: bytes) -> bytes:
    if len(seed) != 32:
        raise ValueError("Seed must be 32 bytes")
    if len(public) != 32:
        raise ValueError("Public key must be 32 bytes")
    h = _H(seed)
    a = _clamp_scalar(h)
    prefix = h[32:]
    r = int.from_bytes(_H(prefix + message), "little") % L_ORDER
    R = _encodepoint(_scalarmult(B, r))
    hram = int.from_bytes(_H(R + public + message), "little") % L_ORDER
    S = (r + hram * a) % L_ORDER
    return R + _encodeint(S)


def verify(signature: bytes, message: bytes, public: bytes) -> bool:
    if len(signature) != 64 or len(public) != 32:
        return False
    try:
        R = _decodepoint(signature[:32])
        A = _decodepoint(public)
    except ValueError:
        return False
    S = _decodeint(signature[32:])
    if S >= L_ORDER:
        return False
    h = int.from_bytes(_H(signature[:32] + public + message), "little") % L_ORDER
    left = _scalarmult(B, S)
    right = _edwards_add(R, _scalarmult(A, h))
    return left == right
