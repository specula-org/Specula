"""Argument validation utilities."""

import jsonschema
from typing import Dict, Any

from .errors import ValidationError


def validate_arguments(arguments: Dict[str, Any],
                      schema: Dict[str, Any]) -> Dict[str, Any]:
    """Validate arguments against JSON schema.

    Args:
        arguments: Arguments to validate
        schema: JSON schema

    Returns:
        Validated arguments (with defaults applied)

    Raises:
        ValidationError: If validation fails
    """
    try:
        # Validate against schema
        jsonschema.validate(instance=arguments, schema=schema)

        # Apply defaults
        validated = _apply_defaults(arguments, schema)

        return validated

    except jsonschema.ValidationError as e:
        raise ValidationError(f"Invalid arguments: {e.message}")
    except jsonschema.SchemaError as e:
        raise ValidationError(f"Invalid schema: {e.message}")


def _apply_defaults(arguments: Dict[str, Any],
                   schema: Dict[str, Any]) -> Dict[str, Any]:
    """Apply default values from schema to arguments.

    Args:
        arguments: Input arguments
        schema: JSON schema with defaults

    Returns:
        Arguments with defaults applied
    """
    result = arguments.copy()

    if "properties" in schema:
        for prop_name, prop_schema in schema["properties"].items():
            if prop_name not in result and "default" in prop_schema:
                result[prop_name] = prop_schema["default"]

    return result
