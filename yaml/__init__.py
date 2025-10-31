"""Local YAML fallback exposing a subset of PyYAML API."""
from __future__ import annotations

from yaml_fallback import safe_dump as _safe_dump
from yaml_fallback import safe_load as _base_safe_load


def safe_load(stream):  # type: ignore[override]
    """Load YAML content from a string or file-like object."""
    if hasattr(stream, "read"):
        stream = stream.read()
    return _base_safe_load(stream)


def safe_dump(data, sort_keys: bool = False):  # type: ignore[override]
    return _safe_dump(data, sort_keys=sort_keys)


__all__ = ["safe_load", "safe_dump"]
