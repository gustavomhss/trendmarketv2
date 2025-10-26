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
import dataclasses
import datetime as _datetime
import re
from typing import Any, Dict, List, Sequence

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

        if "allOf" in schema:
            for subschema in schema["allOf"]:
                self._validate_schema(subschema, instance, path)
        if "anyOf" in schema:
            last_error: ValidationError | None = None
            for subschema in schema["anyOf"]:
                try:
                    self._validate_schema(subschema, instance, path)
                    break
                except ValidationError as exc:
                    last_error = exc
            else:
                raise last_error or ValidationError("anyOf mismatch", path)
        if "oneOf" in schema:
            matches = 0
            last_error: ValidationError | None = None
            for subschema in schema["oneOf"]:
                try:
                    self._validate_schema(subschema, instance, path)
                    matches += 1
                except ValidationError as exc:
                    last_error = exc
            if matches != 1:
                raise last_error or ValidationError("oneOf mismatch", path)
        if "not" in schema:
            try:
                self._validate_schema(schema["not"], instance, path)
            except ValidationError:
                pass
            else:
                raise ValidationError("not schema violated", path)

        if "type" in schema:
            expected_type = schema["type"]
            if isinstance(expected_type, list):
                if not any(self._check_type(candidate, instance) for candidate in expected_type):
                    raise ValidationError(f"Expected type {expected_type}", path)
            else:
                if not self._check_type(expected_type, instance):
                    raise ValidationError(f"Expected type {expected_type}", path)

        if "enum" in schema and instance not in schema["enum"]:
            raise ValidationError(f"Value {instance!r} not in enum", path)

        if "const" in schema and instance != schema["const"]:
            raise ValidationError(f"Value {instance!r} does not match const", path)

        if isinstance(instance, (int, float)) and not isinstance(instance, bool):
            minimum = schema.get("minimum")
            if minimum is not None and instance < minimum:
                raise ValidationError("Value below minimum", path)
            maximum = schema.get("maximum")
            if maximum is not None and instance > maximum:
                raise ValidationError("Value above maximum", path)
            exclusive_min = schema.get("exclusiveMinimum")
            if exclusive_min is not None and instance <= exclusive_min:
                raise ValidationError("Value below exclusiveMinimum", path)
            exclusive_max = schema.get("exclusiveMaximum")
            if exclusive_max is not None and instance >= exclusive_max:
                raise ValidationError("Value above exclusiveMaximum", path)

        if isinstance(instance, str):
            if "minLength" in schema and len(instance) < schema["minLength"]:
                raise ValidationError("String shorter than minLength", path)
            if "maxLength" in schema and len(instance) > schema["maxLength"]:
                raise ValidationError("String longer than maxLength", path)
            if "pattern" in schema and not re.fullmatch(schema["pattern"], instance):
                raise ValidationError("String does not match pattern", path)
            if "format" in schema:
                format_name = schema["format"]
                if not self.format_checker.conforms(format_name, instance):
                    raise ValidationError(f"Invalid format {format_name}", path)

        if isinstance(instance, list):
            if "minItems" in schema and len(instance) < schema["minItems"]:
                raise ValidationError("Array shorter than minItems", path)
            if "maxItems" in schema and len(instance) > schema["maxItems"]:
                raise ValidationError("Array longer than maxItems", path)
            if schema.get("uniqueItems"):
                seen: List[Any] = []
                for item in instance:
                    if item in seen:
                        raise ValidationError("Array items not unique", path)
                    seen.append(item)
            items = schema.get("items")
            if isinstance(items, dict):
                for index, item in enumerate(instance):
                    self._validate_schema(items, item, path + [index])
            elif isinstance(items, list):
                for index, subschema in enumerate(items):
                    if index < len(instance):
                        self._validate_schema(subschema, instance[index], path + [index])
                if schema.get("additionalItems") is False and len(instance) > len(items):
                    raise ValidationError("Additional array items not allowed", path)

        if isinstance(instance, dict):
            properties = schema.get("properties", {})
            required = schema.get("required", [])
            for key in required:
                if key not in instance:
                    raise ValidationError(f"Missing required property {key}", path + [key])
            additional = schema.get("additionalProperties", True)
            if additional is False:
                allowed = set(properties)
                extra = [key for key in instance if key not in allowed]
                if extra:
                    raise ValidationError(f"Additional properties not allowed: {extra}", path)
            elif isinstance(additional, dict):
                for key, value in instance.items():
                    if key not in properties:
                        self._validate_schema(additional, value, path + [key])
            for key, subschema in properties.items():
                if key in instance:
                    self._validate_schema(subschema, instance[key], path + [key])

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
            "null": type(None),
        }
        python_type = mapping.get(expected)
        if python_type is None:
            return True
        if expected in {"number", "integer"} and isinstance(instance, bool):
            return False
        return isinstance(instance, python_type)


def validate(instance: Any, schema: Dict[str, Any]) -> None:
    Draft7Validator(schema).validate(instance)
