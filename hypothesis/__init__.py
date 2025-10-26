from __future__ import annotations

import itertools
from decimal import Decimal
from typing import Any, Dict, Iterable, List, Sequence

from . import strategies as st

__all__ = [
    "given",
    "settings",
    "HealthCheck",
    "Phase",
    "strategies",
]

strategies = st


class HealthCheck:
    too_slow = "too_slow"


class Phase:
    explicit = "explicit"
    reuse = "reuse"
    generate = "generate"


class _Settings:
    def __init__(self) -> None:
        self._profiles: Dict[str, Dict[str, Any]] = {}
        self._active = "default"

    def register_profile(self, name: str, *args: Any, **kwargs: Any) -> None:
        profile: Dict[str, Any] = {}
        if args:
            profile_arg = args[0]
            if isinstance(profile_arg, dict):
                profile.update(profile_arg)
        profile.update(kwargs)
        self._profiles[name] = profile

    def load_profile(self, name: str) -> None:
        self._active = name

    def __call__(self, **kwargs: Any) -> Dict[str, Any]:
        return kwargs


settings = _Settings()


def given(*positional: st._Strategy, **keyword: st._Strategy):
    def decorator(function):
        def wrapper(*args, **kwargs):
            pos_values = [strategy.examples for strategy in positional]
            kw_items = list(keyword.items())
            kw_values = [strategy.examples for _, strategy in kw_items]

            pos_combos: Iterable[Sequence[Any]]
            if pos_values:
                pos_combos = itertools.product(*pos_values)
            else:
                pos_combos = [()]

            kw_combos: Iterable[Sequence[Any]]
            if kw_values:
                kw_combos = itertools.product(*kw_values)
            else:
                kw_combos = [()]

            for pos_combo in pos_combos:
                for kw_combo in kw_combos:
                    local_kwargs = dict(zip((name for name, _ in kw_items), kw_combo))
                    function(*args, *pos_combo, **kwargs, **local_kwargs)

        return wrapper

    return decorator
