"""Minimal JSON Schema Draft-07 validator used offline."""
from __future__ import annotations

import re
from datetime import datetime
from typing import Any, Dict, Iterable, List, Sequence


class ValidationError(Exception):
    """Exception raised when validation fails."""

    def __init__(self, message: str) -> None:
        super().__init__(message)
        self.message = message


def _is_type(instance: Any, expected: str) -> bool:
    if expected == "object":
        return isinstance(instance, dict)
    if expected == "array":
        return isinstance(instance, list)
    if expected == "string":
        return isinstance(instance, str)
    if expected == "integer":
        return isinstance(instance, int) and not isinstance(instance, bool)
    if expected == "number":
        return isinstance(instance, (int, float)) and not isinstance(instance, bool)
    if expected == "boolean":
        return isinstance(instance, bool)
    if expected == "null":
        return instance is None
    return False


def _check_type(instance: Any, schema: Dict[str, Any]) -> None:
    expected = schema.get("type")
    if expected is None:
        return
    if isinstance(expected, list):
        if any(_is_type(instance, item) for item in expected):
            return
    else:
        if _is_type(instance, expected):
            return
    raise ValidationError(f"Tipo inválido: esperado {expected}, recebido {type(instance).__name__}")


def _check_enum(instance: Any, schema: Dict[str, Any]) -> None:
    enum = schema.get("enum")
    if enum is None:
        return
    if instance not in enum:
        raise ValidationError(f"Valor {instance!r} não pertence ao enum {enum}")


def _check_minimum(instance: Any, schema: Dict[str, Any]) -> None:
    minimum = schema.get("minimum")
    if minimum is None:
        return
    if not isinstance(instance, (int, float)):
        raise ValidationError("minimum aplicável apenas a números")
    if instance < minimum:
        raise ValidationError(f"Valor {instance} inferior ao mínimo {minimum}")


def _check_min_length(instance: Any, schema: Dict[str, Any]) -> None:
    min_length = schema.get("minLength")
    if min_length is None:
        return
    if not isinstance(instance, str):
        raise ValidationError("minLength aplicável apenas a strings")
    if len(instance) < min_length:
        raise ValidationError(f"String menor que minLength {min_length}")


def _check_pattern(instance: Any, schema: Dict[str, Any]) -> None:
    pattern = schema.get("pattern")
    if pattern is None:
        return
    if not isinstance(instance, str):
        raise ValidationError("pattern aplicável apenas a strings")
    if not re.fullmatch(pattern, instance):
        raise ValidationError(f"String {instance!r} não corresponde ao padrão {pattern!r}")


def _check_format(instance: Any, schema: Dict[str, Any]) -> None:
    format_name = schema.get("format")
    if format_name is None or instance is None:
        return
    if format_name == "date-time":
        if not isinstance(instance, str):
            raise ValidationError("date-time requer string")
        candidate = instance
        if candidate.endswith("Z"):
            candidate = candidate[:-1] + "+00:00"
        try:
            datetime.fromisoformat(candidate)
        except ValueError as exc:
            raise ValidationError(f"date-time inválido: {instance}") from exc


def _validate_properties(instance: Dict[str, Any], schema: Dict[str, Any]) -> None:
    required: Sequence[str] = schema.get("required", [])
    for key in required:
        if key not in instance:
            raise ValidationError(f"Campo obrigatório ausente: {key}")
    properties: Dict[str, Dict[str, Any]] = schema.get("properties", {})
    additional = schema.get("additionalProperties", True)
    for key, value in instance.items():
        if key in properties:
            _validate(value, properties[key])
        else:
            if additional is False:
                raise ValidationError(f"Propriedade não permitida: {key}")
            if isinstance(additional, dict):
                _validate(value, additional)


def _validate_array(instance: List[Any], schema: Dict[str, Any]) -> None:
    min_items = schema.get("minItems")
    if min_items is not None and len(instance) < min_items:
        raise ValidationError(f"Array com tamanho {len(instance)} menor que minItems {min_items}")
    items_schema = schema.get("items")
    if isinstance(items_schema, dict):
        for index, item in enumerate(instance):
            try:
                _validate(item, items_schema)
            except ValidationError as exc:
                raise ValidationError(f"Item {index}: {exc.message}") from exc


def _validate(instance: Any, schema: Dict[str, Any]) -> None:
    _check_type(instance, schema)
    _check_enum(instance, schema)
    if isinstance(instance, (int, float)):
        _check_minimum(instance, schema)
    if isinstance(instance, str):
        _check_min_length(instance, schema)
        _check_pattern(instance, schema)
        _check_format(instance, schema)
    if isinstance(instance, dict):
        _validate_properties(instance, schema)
    if isinstance(instance, list):
        _validate_array(instance, schema)


def validate(instance: Any, schema: Dict[str, Any]) -> None:
    """Validate instance against schema raising ValidationError on failure."""
    _validate(instance, schema)


__all__ = ["validate", "ValidationError"]
