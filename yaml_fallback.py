"""Minimal YAML reader/writer used when PyYAML is unavailable."""

from __future__ import annotations

import json
from typing import Any, List, Tuple


class YAMLError(Exception):
    """Fallback exception matching PyYAML's API."""


def _strip_comment(line: str) -> str:
    if "#" not in line:
        return line
    in_quote = False
    quote_char = ""
    for idx, char in enumerate(line):
        if char in {'"', "'"}:
            if not in_quote:
                in_quote = True
                quote_char = char
            elif quote_char == char:
                in_quote = False
        if char == "#" and not in_quote:
            return line[:idx]
    return line


def _tokenize(text: str) -> List[Tuple[int, str]]:
    tokens: List[Tuple[int, str]] = []
    for raw_line in text.splitlines():
        line = _strip_comment(raw_line.rstrip())
        if not line.strip() or line.strip() == "---":
            continue
        indent = len(line) - len(line.lstrip(" "))
        tokens.append((indent, line.lstrip()))
    return tokens


def _parse_scalar(token: str) -> Any:
    token = token.strip()
    if not token:
        return None
    lowered = token.lower()
    if lowered in {"null", "none"}:
        return None
    if lowered == "true":
        return True
    if lowered == "false":
        return False
    if token.startswith("'") and token.endswith("'"):
        return token[1:-1]
    if token.startswith('"') and token.endswith('"'):
        return token[1:-1]
    try:
        return int(token)
    except ValueError:
        try:
            return float(token)
        except ValueError:
            return token


def _parse_block(
    tokens: List[Tuple[int, str]], index: int, indent: int
) -> Tuple[Any, int]:
    if index >= len(tokens):
        return None, index
    current_indent, content = tokens[index]
    if current_indent < indent:
        return None, index
    if content.startswith("- ") or content == "-":
        items: List[Any] = []
        while index < len(tokens):
            level, entry = tokens[index]
            if level < indent or not entry.startswith("-"):
                break
            entry_content = entry[1:].lstrip()
            if not entry_content:
                index += 1
                value, index = _parse_block(tokens, index, level + 2)
                items.append(value)
                continue
            if ":" in entry_content:
                key, rest = entry_content.split(":", 1)
                mapping: dict[str, Any] = {}
                if rest.strip():
                    mapping[key.strip()] = _parse_scalar(rest.strip())
                    index += 1
                else:
                    index += 1
                    value, index = _parse_block(tokens, index, level + 2)
                    mapping[key.strip()] = value
                while index < len(tokens):
                    sub_level, sub_content = tokens[index]
                    if sub_level <= level:
                        break
                    if sub_content.startswith("-"):
                        break
                    sub_key, sub_rest = sub_content.split(":", 1)
                    if sub_rest.strip():
                        mapping[sub_key.strip()] = _parse_scalar(sub_rest.strip())
                        index += 1
                    else:
                        index += 1
                        nested, index = _parse_block(tokens, index, sub_level + 2)
                        mapping[sub_key.strip()] = nested
                items.append(mapping)
            else:
                items.append(_parse_scalar(entry_content))
                index += 1
        return items, index
    mapping: dict[str, Any] = {}
    while index < len(tokens):
        level, entry = tokens[index]
        if level < indent:
            break
        if entry.startswith("-"):
            break
        if ":" not in entry:
            raise ValueError(f"Invalid mapping line: {entry}")
        key, rest = entry.split(":", 1)
        key = key.strip()
        rest = rest.strip()
        if rest:
            mapping[key] = _parse_scalar(rest)
            index += 1
        else:
            index += 1
            value, index = _parse_block(tokens, index, level + 2)
            mapping[key] = value
    return mapping, index


def safe_load(text: str) -> Any:
    stripped = text.strip()
    if not stripped:
        return None
    try:
        return json.loads(stripped)
    except json.JSONDecodeError:
        pass
    tokens = _tokenize(text)
    if not tokens:
        return None
    value, _ = _parse_block(tokens, 0, tokens[0][0])
    return value


def _format_scalar(value: Any) -> str:
    if value is None:
        return "null"
    if isinstance(value, bool):
        return "true" if value else "false"
    if isinstance(value, (int, float)):
        return str(value)
    text = str(value)
    if not text:
        return "''"
    if any(ch in text for ch in ("#", ":", "\n")) or text.strip() != text:
        return '"' + text.replace('"', '\\"') + '"'
    return text


def _dump(obj: Any, indent: int, lines: List[str], sort_keys: bool) -> None:
    prefix = " " * indent
    if isinstance(obj, dict):
        keys = sorted(obj.keys()) if sort_keys else obj.keys()
        for key in keys:
            value = obj[key]
            if isinstance(value, (dict, list)):
                lines.append(f"{prefix}{key}:")
                _dump(value, indent + 2, lines, sort_keys)
            else:
                lines.append(f"{prefix}{key}: {_format_scalar(value)}")
    elif isinstance(obj, list):
        for item in obj:
            if isinstance(item, (dict, list)):
                lines.append(f"{prefix}-")
                _dump(item, indent + 2, lines, sort_keys)
            else:
                lines.append(f"{prefix}- {_format_scalar(item)}")
    else:
        lines.append(f"{prefix}{_format_scalar(obj)}")


def safe_dump(obj: Any, sort_keys: bool = False) -> str:
    lines: List[str] = []
    _dump(obj, 0, lines, sort_keys)
    return "\n".join(lines) + "\n"


__all__ = ["safe_load", "safe_dump"]
