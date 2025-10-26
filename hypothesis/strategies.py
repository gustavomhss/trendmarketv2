from __future__ import annotations

from decimal import Decimal
from typing import List


class Strategy:
    def draw(self, rng, iteration: int):  # pragma: no cover - abstract
        raise NotImplementedError


class IntegerStrategy(Strategy):
    def __init__(self, min_value: int | None, max_value: int | None) -> None:
        self.min = int(min_value if min_value is not None else -100)
        self.max = int(max_value if max_value is not None else 100)
        if self.min > self.max:
            self.min, self.max = self.max, self.min
        base_values: List[int] = [self.min, self.max]
        if self.min <= 0 <= self.max:
            base_values.append(0)
        if self.min <= 1 <= self.max:
            base_values.append(1)
        if self.min <= -1 <= self.max:
            base_values.append(-1)
        self.base_values = list(dict.fromkeys(base_values))

    def draw(self, rng, iteration: int) -> int:
        if self.base_values and iteration < len(self.base_values):
            return self.base_values[iteration]
        return rng.randint(self.min, self.max)


class DecimalStrategy(Strategy):
    def __init__(
        self,
        min_value: Decimal | int | float | None,
        max_value: Decimal | int | float | None,
        places: int | None,
    ) -> None:
        self.places = int(places if places is not None else 6)
        self.quant = Decimal(1).scaleb(-self.places)
        self.min_val = self._coerce(min_value, Decimal(-10))
        self.max_val = self._coerce(max_value, Decimal(10))
        if self.min_val > self.max_val:
            self.min_val, self.max_val = self.max_val, self.min_val
        self.base_values: List[Decimal] = [self.min_val, self.max_val]
        for candidate in [Decimal(0), self.quant, -self.quant]:
            if self.min_val <= candidate <= self.max_val:
                self.base_values.append(candidate)
        self.base_values = [self._quantize(value) for value in dict.fromkeys(self.base_values)]

    def _coerce(self, value, default: Decimal) -> Decimal:
        if value is None:
            return default
        if isinstance(value, Decimal):
            return value
        return Decimal(str(value))

    def _quantize(self, value: Decimal) -> Decimal:
        return value.quantize(self.quant)

    def draw(self, rng, iteration: int) -> Decimal:
        if self.base_values and iteration < len(self.base_values):
            return self.base_values[iteration]
        span = int(((self.max_val - self.min_val) / self.quant))
        if span <= 0:
            return self._quantize(self.min_val)
        step = rng.randint(0, span)
        return self._quantize(self.min_val + self.quant * step)


def integers(min_value: int | None = None, max_value: int | None = None, **_: object) -> Strategy:
    return IntegerStrategy(min_value, max_value)


def decimals(
    *,
    min_value: Decimal | int | float | None = None,
    max_value: Decimal | int | float | None = None,
    places: int | None = None,
    allow_nan: bool | None = None,
    allow_infinity: bool | None = None,
) -> Strategy:
    _ = allow_nan, allow_infinity
    return DecimalStrategy(min_value, max_value, places)
