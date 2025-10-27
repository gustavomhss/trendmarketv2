from __future__ import annotations

import datetime as _datetime
import re
from typing import Any, Dict, List, Sequence

__all__ = ['Draft7Validator', 'ValidationError', 'FormatChecker', 'validate']


class ValidationError(Exception):
    def __init__(self, message: str, path: Sequence[Any] | None = None) -> None:
        super().__init__(message)
        self.message = message
        self.path: List[Any] = list(path or [])


class FormatChecker:
    def __init__(self) -> None:
        self._checks: Dict[str, Any] = {}

    def conforms(self, format_name: str, value: Any) -> bool:
        if format_name == 'date-time':
            if not isinstance(value, str):
                return False
            try:
                if value.endswith('Z'):
                    _datetime.datetime.fromisoformat(value.replace('Z', '+00:00'))
                else:
                    _datetime.datetime.fromisoformat(value)
                return True
            except ValueError:
                return False
        check = self._checks.get(format_name)
        if check is None:
            return True
        return bool(check(value))


class Draft7Validator:
    def __init__(self, schema: Dict[str, Any], format_checker: FormatChecker | None = None) -> None:
        self.schema = schema
        self.format_checker = format_checker or FormatChecker()

    def validate(self, instance: Any) -> None:
        self._validate_schema(self.schema, instance, [])

    def _validate_schema(self, schema: Dict[str, Any], instance: Any, path: List[Any]) -> None:
        if '$ref' in schema:
            ref = schema['$ref']
            resolved = self._resolve_ref(ref)
            self._validate_schema(resolved, instance, path)
            return

        if 'allOf' in schema:
            for subschema in schema['allOf']:
                self._validate_schema(subschema, instance, path)
        if 'anyOf' in schema:
            last_error: ValidationError | None = None
            for subschema in schema['anyOf']:
                try:
                    self._validate_schema(subschema, instance, path)
                    break
                except ValidationError as exc:
                    last_error = exc
            else:
                raise last_error or ValidationError('anyOf mismatch', path)
        if 'oneOf' in schema:
            matches = 0
            last_error: ValidationError | None = None
            for subschema in schema['oneOf']:
                try:
                    self._validate_schema(subschema, instance, path)
                    matches += 1
                except ValidationError as exc:
                    last_error = exc
            if matches != 1:
                raise last_error or ValidationError('oneOf mismatch', path)
        if 'not' in schema:
            try:
                self._validate_schema(schema['not'], instance, path)
            except ValidationError:
                pass
            else:
                raise ValidationError('not schema violated', path)

        if 'type' in schema:
            expected_type = schema['type']
            if isinstance(expected_type, list):
                if not any(self._check_type(candidate, instance) for candidate in expected_type):
                    raise ValidationError(f'Expected type {expected_type}', path)
            else:
                if not self._check_type(expected_type, instance):
                    raise ValidationError(f'Expected type {expected_type}', path)

        if 'enum' in schema and instance not in schema['enum']:
            raise ValidationError(f"Value {instance!r} not in enum", path)

        if 'const' in schema and instance != schema['const']:
            raise ValidationError(f"Value {instance!r} does not match const", path)

        if isinstance(instance, (int, float)) and not isinstance(instance, bool):
            minimum = schema.get('minimum')
            if minimum is not None and instance < minimum:
                raise ValidationError('Value below minimum', path)
            maximum = schema.get('maximum')
            if maximum is not None and instance > maximum:
                raise ValidationError('Value above maximum', path)
            exclusive_min = schema.get('exclusiveMinimum')
            if exclusive_min is not None and instance <= exclusive_min:
                raise ValidationError('Value below exclusiveMinimum', path)
            exclusive_max = schema.get('exclusiveMaximum')
            if exclusive_max is not None and instance >= exclusive_max:
                raise ValidationError('Value above exclusiveMaximum', path)

        if isinstance(instance, str):
            if 'minLength' in schema and len(instance) < schema['minLength']:
                raise ValidationError('String shorter than minLength', path)
            if 'maxLength' in schema and len(instance) > schema['maxLength']:
                raise ValidationError('String longer than maxLength', path)
            if 'pattern' in schema and not re.fullmatch(schema['pattern'], instance):
                raise ValidationError('String does not match pattern', path)
            if 'format' in schema:
                format_name = schema['format']
                if not self.format_checker.conforms(format_name, instance):
                    raise ValidationError(f'Invalid format {format_name}', path)

        if isinstance(instance, list):
            if 'minItems' in schema and len(instance) < schema['minItems']:
                raise ValidationError('Array shorter than minItems', path)
            if 'maxItems' in schema and len(instance) > schema['maxItems']:
                raise ValidationError('Array longer than maxItems', path)
            if schema.get('uniqueItems'):
                seen: List[Any] = []
                for item in instance:
                    if item in seen:
                        raise ValidationError('Array items not unique', path)
                    seen.append(item)
            items = schema.get('items')
            if isinstance(items, dict):
                for index, item in enumerate(instance):
                    self._validate_schema(items, item, path + [index])
            elif isinstance(items, list):
                for index, subschema in enumerate(items):
                    if index < len(instance):
                        self._validate_schema(subschema, instance[index], path + [index])
                if schema.get('additionalItems') is False and len(instance) > len(items):
                    raise ValidationError('Additional array items not allowed', path)

        if isinstance(instance, dict):
            properties = schema.get('properties', {})
            required = schema.get('required', [])
            for key in required:
                if key not in instance:
                    raise ValidationError(f'Missing required property {key}', path + [key])
            additional = schema.get('additionalProperties', True)
            if additional is False:
                allowed = set(properties)
                extra = [key for key in instance if key not in allowed]
                if extra:
                    raise ValidationError(f'Additional properties not allowed: {extra}', path)
            elif isinstance(additional, dict):
                for key, value in instance.items():
                    if key not in properties:
                        self._validate_schema(additional, value, path + [key])
            for key, subschema in properties.items():
                if key in instance:
                    self._validate_schema(subschema, instance[key], path + [key])

    def _resolve_ref(self, ref: str) -> Dict[str, Any]:
        if not ref.startswith('#/'):
            raise ValidationError(f'Unsupported $ref: {ref}')
        parts = ref[2:].split('/')
        node: Any = self.schema
        for part in parts:
            if not isinstance(node, dict) or part not in node:
                raise ValidationError(f'Unresolvable $ref: {ref}')
            node = node[part]
        if not isinstance(node, dict):
            raise ValidationError(f'$ref {ref} did not resolve to object')
        return node

    @staticmethod
    def _check_type(expected: str, instance: Any) -> bool:
        mapping = {
            'object': dict,
            'string': str,
            'number': (int, float),
            'integer': int,
            'boolean': bool,
            'array': list,
            'null': type(None),
        }
        python_type = mapping.get(expected)
        if python_type is None:
            return True
        if expected in {'number', 'integer'} and isinstance(instance, bool):
            return False
        return isinstance(instance, python_type)


def validate(instance: Any, schema: Dict[str, Any]) -> None:
    Draft7Validator(schema).validate(instance)
