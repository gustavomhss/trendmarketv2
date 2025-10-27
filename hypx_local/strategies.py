from __future__ import annotations

from decimal import Decimal, ROUND_HALF_EVEN
from typing import Iterable, List

__all__ = ["decimals", "integers", "_Strategy"]


class _Strategy:
    def __init__(self, examples: Iterable):
        self.examples = list(examples)
        if not self.examples:
            self.examples = [None]


def _decimal(value: Decimal, places: int) -> Decimal:
    quant = Decimal("1").scaleb(-places)
    return value.quantize(quant, rounding=ROUND_HALF_EVEN)


def decimals(
    *,
    min_value: Decimal | float,
    max_value: Decimal | float,
    places: int,
    allow_nan: bool = False,
    allow_infinity: bool = False,
) -> _Strategy:
    lower = Decimal(str(min_value))
    upper = Decimal(str(max_value))
    midpoint = _decimal((lower + upper) / 2, places)
    step = Decimal("1").scaleb(-places)
    values: List[Decimal] = [lower, upper, midpoint]
    values.append(_decimal(lower + step, places))
    values.append(_decimal(upper - step, places))
    unique = []
    for value in values:
        if lower <= value <= upper and value not in unique:
            unique.append(value)
    return _Strategy(unique)


def integers(min_value: int, max_value: int) -> _Strategy:
    values = [min_value, max_value]
    mid = (min_value + max_value) // 2
    values.append(mid)
    return _Strategy(sorted(set(values)))
