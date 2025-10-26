from __future__ import annotations

import dataclasses
import datetime as _datetime
import json
import re
from typing import Any, Dict, Iterable, List, Sequence

__all__ = ["Draft7Validator", "ValidationError", "FormatChecker", "validate"]


class ValidationError(Exception):
    def __init__(self, message: str, path: Sequence[Any] | None = None) -> None:
        super().__init__(message)
        self.message = message
        self.path: List[Any] = list(path or [])


class FormatChecker:
    def __init__(self) -> None:
        self._checks: Dict[str, Any] = {}

    def conforms(self, format_name: str, value: Any) -> bool:
        if format_name == "date-time":
            if not isinstance(value, str):
                return False
            try:
                if value.endswith("Z"):
                    _datetime.datetime.fromisoformat(value.replace("Z", "+00:00"))
                else:
                    _datetime.datetime.fromisoformat(value)
                return True
            except ValueError:
                return False
        check = self._checks.get(format_name)
        if check is None:
            return True
        return bool(check(value))


@dataclasses.dataclass
class _SchemaContext:
    schema: Dict[str, Any]
    format_checker: FormatChecker


class Draft7Validator:
    def __init__(self, schema: Dict[str, Any], format_checker: FormatChecker | None = None) -> None:
        self.schema = schema
        self.format_checker = format_checker or FormatChecker()

    def validate(self, instance: Any) -> None:
        self._validate_schema(self.schema, instance, [])

    def _validate_schema(self, schema: Dict[str, Any], instance: Any, path: List[Any]) -> None:
        if "$ref" in schema:
            ref = schema["$ref"]
            resolved = self._resolve_ref(ref)
            self._validate_schema(resolved, instance, path)
            return

        if "type" in schema:
            expected_type = schema["type"]
            if not self._check_type(expected_type, instance):
                raise ValidationError(f"Expected type {expected_type}", path)

        if isinstance(instance, dict):
            properties = schema.get("properties", {})
            required = schema.get("required", [])
            for key in required:
                if key not in instance:
                    raise ValidationError(f"Missing required property {key}", path + [key])
            if schema.get("additionalProperties") is False:
                allowed = set(properties)
                extra = [key for key in instance if key not in allowed]
                if extra:
                    raise ValidationError(f"Additional properties not allowed: {extra}", path)
            for key, subschema in properties.items():
                if key in instance:
                    self._validate_schema(subschema, instance[key], path + [key])

        if isinstance(instance, list) and "items" in schema:
            subschema = schema["items"]
            for index, item in enumerate(instance):
                self._validate_schema(subschema, item, path + [index])

        if "enum" in schema and instance not in schema["enum"]:
            raise ValidationError(f"Value {instance!r} not in enum", path)

        if "const" in schema and instance != schema["const"]:
            raise ValidationError(f"Value {instance!r} does not match const", path)

        if isinstance(instance, (int, float)):
            if "minimum" in schema and instance < schema["minimum"]:
                raise ValidationError("Value below minimum", path)
            if "maximum" in schema and instance > schema["maximum"]:
                raise ValidationError("Value above maximum", path)

        if isinstance(instance, str) and "pattern" in schema:
            if not re.fullmatch(schema["pattern"], instance):
                raise ValidationError("String does not match pattern", path)

        if isinstance(instance, str) and "format" in schema:
            format_name = schema["format"]
            if not self.format_checker.conforms(format_name, instance):
                raise ValidationError(f"Invalid format {format_name}", path)

    def _resolve_ref(self, ref: str) -> Dict[str, Any]:
        if not ref.startswith("#/"):
            raise ValidationError(f"Unsupported $ref: {ref}")
        parts = ref[2:].split("/")
        node: Any = self.schema
        for part in parts:
            if not isinstance(node, dict) or part not in node:
                raise ValidationError(f"Unresolvable $ref: {ref}")
            node = node[part]
        if not isinstance(node, dict):
            raise ValidationError(f"$ref {ref} did not resolve to object")
        return node

    @staticmethod
    def _check_type(expected: str, instance: Any) -> bool:
        mapping = {
            "object": dict,
            "string": str,
            "number": (int, float),
            "integer": int,
            "boolean": bool,
            "array": list,
        }
        python_type = mapping.get(expected)
        if python_type is None:
            return True
        if expected == "number" and isinstance(instance, bool):
            return False
        if expected == "integer" and isinstance(instance, bool):
            return False
        return isinstance(instance, python_type)


def validate(instance: Any, schema: Dict[str, Any]) -> None:
    Draft7Validator(schema).validate(instance)
