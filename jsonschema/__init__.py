from __future__ import annotations

import re
from datetime import datetime
from typing import Any, Dict, Iterable, List


class ValidationError(Exception):
    def __init__(self, message: str, path: Iterable[str] | None = None) -> None:
        super().__init__(message)
        self.message = message
        self.path = list(path or [])


class _Resolver:
    def __init__(self, root: Dict[str, Any]) -> None:
        self.root = root

    def resolve(self, ref: str) -> Dict[str, Any]:
        if not ref.startswith("#/"):
            raise ValidationError(f"Unsupported $ref: {ref}")
        node: Any = self.root
        for segment in ref.lstrip("#/").split("/"):
            if isinstance(node, dict) and segment in node:
                node = node[segment]
            else:
                raise ValidationError(f"$ref path not found: {ref}")
        if not isinstance(node, dict):
            raise ValidationError(f"$ref must resolve to object: {ref}")
        return node


def validate(instance: Any, schema: Dict[str, Any]) -> None:
    resolver = _Resolver(schema)
    _validate(instance, schema, resolver, [])


def _validate(instance: Any, schema: Dict[str, Any], resolver: _Resolver, path: List[str]) -> None:
    if "$ref" in schema:
        _validate(instance, resolver.resolve(schema["$ref"]), resolver, path)
        return

    if "allOf" in schema:
        for sub_schema in schema["allOf"]:
            _validate(instance, sub_schema, resolver, path)

    schema_type = schema.get("type")
    if schema_type is not None:
        _check_type(instance, schema_type, path)

    if "enum" in schema and instance not in schema["enum"]:
        raise ValidationError(f"Value {instance!r} not in enum", path)

    if "const" in schema and instance != schema["const"]:
        raise ValidationError(f"Value {instance!r} must equal {schema['const']!r}", path)

    if "pattern" in schema:
        if not isinstance(instance, str):
            raise ValidationError("Pattern applies to strings", path)
        if re.fullmatch(schema["pattern"], instance) is None:
            raise ValidationError(f"String {instance!r} does not match pattern", path)

    if "minLength" in schema:
        if not isinstance(instance, str) or len(instance) < schema["minLength"]:
            raise ValidationError("String shorter than minLength", path)

    if "minimum" in schema:
        if not isinstance(instance, (int, float)):
            raise ValidationError("minimum requires numeric value", path)
        if instance < schema["minimum"]:
            raise ValidationError("Value below minimum", path)

    if schema.get("format") == "date-time":
        if not isinstance(instance, str):
            raise ValidationError("date-time requires string", path)
        candidate = instance.replace("Z", "+00:00")
        try:
            datetime.fromisoformat(candidate)
        except ValueError:
            raise ValidationError("Invalid date-time", path)

    if schema_type == "object" or (isinstance(schema_type, list) and "object" in schema_type):
        if not isinstance(instance, dict):
            raise ValidationError("Expected object", path)
        properties = schema.get("properties", {})
        required = schema.get("required", [])
        for key in required:
            if key not in instance:
                raise ValidationError(f"Missing required property: {key}", path + [key])
        additional = schema.get("additionalProperties", True)
        if additional is False:
            extra_keys = [key for key in instance if key not in properties]
            if extra_keys:
                raise ValidationError(f"Additional properties not allowed: {extra_keys}", path)
        for key, value in instance.items():
            if key in properties:
                _validate(value, properties[key], resolver, path + [key])

    if schema_type == "array" or (isinstance(schema_type, list) and "array" in schema_type):
        if not isinstance(instance, list):
            raise ValidationError("Expected array", path)
        min_items = schema.get("minItems")
        if min_items is not None and len(instance) < min_items:
            raise ValidationError("Array shorter than minItems", path)
        items_schema = schema.get("items")
        if isinstance(items_schema, dict):
            for index, item in enumerate(instance):
                _validate(item, items_schema, resolver, path + [str(index)])


def _check_type(instance: Any, schema_type: Any, path: List[str]) -> None:
    allowed: List[str]
    if isinstance(schema_type, list):
        allowed = schema_type
    else:
        allowed = [schema_type]
    for t in allowed:
        if _matches_type(instance, t):
            return
    raise ValidationError(f"Type mismatch, expected {allowed}", path)


def _matches_type(instance: Any, schema_type: str) -> bool:
    if schema_type == "object":
        return isinstance(instance, dict)
    if schema_type == "array":
        return isinstance(instance, list)
    if schema_type == "string":
        return isinstance(instance, str)
    if schema_type == "integer":
        return isinstance(instance, int) and not isinstance(instance, bool)
    if schema_type == "number":
        return isinstance(instance, (int, float)) and not isinstance(instance, bool)
    if schema_type == "boolean":
        return isinstance(instance, bool)
    if schema_type == "null":
        return instance is None
    return True
