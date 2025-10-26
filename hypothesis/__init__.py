from __future__ import annotations

import os
import random
from typing import Any, Callable, Dict, List, Tuple

from . import strategies


class SettingsRegistry:
    def __init__(self) -> None:
        self._profiles: Dict[str, Dict[str, Any]] = {}
        self._current: Dict[str, Any] = {"max_examples": 10}

    def register_profile(self, name: str, **kwargs: Any) -> None:
        self._profiles[name] = dict(kwargs)

    def load_profile(self, name: str) -> None:
        profile = self._profiles.get(name)
        if profile is None:
            raise KeyError(f"Hypothesis profile not registered: {name}")
        self._current.update(profile)

    def get(self, key: str, default: Any = None) -> Any:
        return self._current.get(key, default)


settings = SettingsRegistry()


def _resolve_seed(explicit: Any) -> int:
    if explicit is not None:
        try:
            return int(explicit)
        except (TypeError, ValueError):
            pass
    env_seed = os.getenv("HYPOTHESIS_SEED")
    if env_seed is not None:
        try:
            return int(env_seed)
        except ValueError:
            pass
    profile_seed = settings.get("seed")
    if profile_seed is not None:
        try:
            return int(profile_seed)
        except (TypeError, ValueError):
            pass
    return 0


def given(*strategies_args: strategies.Strategy, **strategies_kwargs: strategies.Strategy) -> Callable[[Callable[..., Any]], Callable[..., Any]]:
    def decorator(test_func: Callable[..., Any]) -> Callable[..., Any]:
        def wrapper(*args: Any, **kwargs: Any) -> Any:
            max_examples = settings.get("max_examples", 10)
            max_examples = int(max_examples)
            seed = _resolve_seed(strategies_kwargs.get("seed"))
            rng = random.Random(seed)
            arg_strategies: Tuple[strategies.Strategy, ...] = strategies_args
            kw_strategies: Dict[str, strategies.Strategy] = strategies_kwargs.copy()
            kw_strategies.pop("seed", None)
            for example_index in range(max_examples):
                drawn_args: List[Any] = [strategy.draw(rng, example_index) for strategy in arg_strategies]
                drawn_kwargs: Dict[str, Any] = {
                    name: strategy.draw(rng, example_index) for name, strategy in kw_strategies.items()
                }
                test_func(*args, *drawn_args, **kwargs, **drawn_kwargs)
        wrapper.__name__ = getattr(test_func, "__name__", "hypothesis_wrapped")
        wrapper.__qualname__ = getattr(test_func, "__qualname__", wrapper.__name__)
        wrapper.__doc__ = getattr(test_func, "__doc__", None)
        wrapper.__module__ = getattr(test_func, "__module__", __name__)
        return wrapper

    return decorator


__all__ = ["given", "settings", "strategies"]
