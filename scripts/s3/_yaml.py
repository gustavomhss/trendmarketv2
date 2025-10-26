"""Minimal YAML loader supporting a subset used in gatecheck configs."""
from __future__ import annotations

from pathlib import Path
from typing import Any, List, Tuple


def _parse_scalar(value: str) -> Any:
    if value in {"true", "True"}:
        return True
    if value in {"false", "False"}:
        return False
    if value in {"null", "~"}:
        return None
    try:
        if value.startswith("0") and value not in {"0", "0.0"}:
            raise ValueError
        return int(value)
    except ValueError:
        try:
            return float(value)
        except ValueError:
            if value.startswith("[") and value.endswith("]"):
                inner = value[1:-1].strip()
                if not inner:
                    return []
                return [item.strip().strip('"\'') for item in inner.split(",")]
            return value.strip('"\'')


def _parse_block(lines: List[str], idx: int, indent: int) -> Tuple[Any, int]:
    mapping = {}
    sequence: List[Any] = []
    mode = None  # None -> unknown, 'map', 'seq'
    while idx < len(lines):
        raw = lines[idx]
        stripped = raw.strip()
        if not stripped or stripped.startswith("#"):
            idx += 1
            continue
        current_indent = len(raw) - len(raw.lstrip(" "))
        if current_indent < indent:
            break
        if stripped.startswith("- "):
            if mode == "map":
                raise ValueError("cannot mix sequence and mapping")
            mode = "seq"
            value_part = stripped[2:].strip()
            idx += 1
            if value_part:
                if ":" in value_part:
                    synthetic = [" " * (current_indent + 2) + value_part]
                    cursor = idx
                    while cursor < len(lines):
                        nxt = lines[cursor]
                        nxt_indent = len(nxt) - len(nxt.lstrip(" "))
                        if nxt_indent <= current_indent:
                            break
                        synthetic.append(nxt)
                        cursor += 1
                    value, _ = _parse_block(synthetic, 0, current_indent + 2)
                    sequence.append(value)
                    idx = cursor
                else:
                    sequence.append(_parse_scalar(value_part))
            else:
                value, idx = _parse_block(lines, idx, current_indent + 2)
                sequence.append(value)
        else:
            if mode == "seq":
                raise ValueError("cannot mix sequence and mapping")
            mode = "map"
            if ":" not in stripped:
                raise ValueError(f"invalid mapping line: {raw!r}")
            key, value_part = stripped.split(":", 1)
            key = key.strip()
            value_part = value_part.strip()
            idx += 1
            if value_part:
                mapping[key] = _parse_scalar(value_part)
            else:
                value, idx = _parse_block(lines, idx, current_indent + 2)
                mapping[key] = value
    return (sequence if mode == "seq" else mapping), idx


def loads(text: str) -> Any:
    lines = text.splitlines()
    data, _ = _parse_block(lines, 0, 0)
    return data


def load(path: Path) -> Any:
    return loads(path.read_text(encoding="utf-8"))


__all__ = ["load", "loads"]
