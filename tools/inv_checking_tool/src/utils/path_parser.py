"""Path parsing utilities for accessing nested TLA+ state variables.

This module provides utilities to parse path expressions like:
- "log.s1.entries[0].term"
- "currentTerm.s1"
- "config[s1].jointConfig[0]"

And retrieve values from nested Python data structures.
"""

import re
from typing import Any, List, Union


# Pattern to match path segments with optional array index
# Matches: "name", "name[0]", "name[key]"
PATH_SEGMENT_PATTERN = re.compile(
    r'([a-zA-Z_][a-zA-Z0-9_]*)'  # Variable name
    r'(?:\[([^\]]+)\])?'         # Optional index in brackets
)


class PathParseError(Exception):
    """Exception raised when path parsing fails."""
    pass


class PathAccessError(Exception):
    """Exception raised when path access fails."""
    pass


def parse_variable_path(path: str) -> List[Union[str, int]]:
    """Parse a dot-separated path into a list of keys/indices.

    Supports the following path formats:
    - "variable" -> ["variable"]
    - "a.b.c" -> ["a", "b", "c"]
    - "a[0].b" -> ["a", 0, "b"]
    - "a[key].b" -> ["a", "key", "b"]
    - "a.b[0][1]" -> ["a", "b", 0, 1]

    Args:
        path: A dot-separated path string.

    Returns:
        A list of string keys and integer indices.

    Raises:
        PathParseError: If the path format is invalid.

    Examples:
        >>> parse_variable_path("log.s1.entries[0].term")
        ['log', 's1', 'entries', 0, 'term']
        >>> parse_variable_path("currentTerm.s1")
        ['currentTerm', 's1']
    """
    if not path:
        raise PathParseError("Empty path")

    parts = []

    # Split by dots, but handle brackets specially
    segments = path.split('.')

    for segment in segments:
        if not segment:
            raise PathParseError(f"Empty segment in path: {path}")

        # Handle multiple brackets in one segment: a[0][1]
        remaining = segment
        first_in_segment = True

        while remaining:
            # Check for leading bracket (for subsequent indices)
            if remaining.startswith('['):
                bracket_end = remaining.find(']')
                if bracket_end == -1:
                    raise PathParseError(f"Unclosed bracket in path: {path}")

                index_str = remaining[1:bracket_end]
                remaining = remaining[bracket_end + 1:]

                # Try to parse as integer
                try:
                    parts.append(int(index_str))
                except ValueError:
                    # Keep as string key
                    parts.append(index_str)
                continue

            # Match variable name with optional index
            match = PATH_SEGMENT_PATTERN.match(remaining)
            if not match:
                raise PathParseError(f"Invalid path segment: {remaining}")

            name, index = match.groups()
            parts.append(name)

            if index is not None:
                # Try to parse as integer
                try:
                    parts.append(int(index))
                except ValueError:
                    # Keep as string key
                    parts.append(index)

            remaining = remaining[match.end():]
            first_in_segment = False

    return parts


def get_value_at_path(data: Any, path: Union[str, List[Union[str, int]]]) -> Any:
    """Get a value from nested data structure using a path.

    Args:
        data: The root data structure (dict, list, or nested combination).
        path: Either a path string or a pre-parsed list of keys/indices.

    Returns:
        The value at the specified path.

    Raises:
        PathAccessError: If the path cannot be traversed.

    Examples:
        >>> data = {"log": {"s1": {"entries": [{"term": 1}]}}}
        >>> get_value_at_path(data, "log.s1.entries[0].term")
        1
    """
    if isinstance(path, str):
        path = parse_variable_path(path)

    current = data
    traversed = []

    for part in path:
        traversed.append(str(part))
        try:
            if isinstance(current, dict):
                if part not in current:
                    # Try string conversion for integer keys
                    str_part = str(part)
                    if str_part in current:
                        current = current[str_part]
                    else:
                        available = list(current.keys())[:10]
                        raise PathAccessError(
                            f"Key '{part}' not found at path '{'.'.join(traversed[:-1])}'. "
                            f"Available keys: {available}"
                        )
                else:
                    current = current[part]
            elif isinstance(current, (list, tuple)):
                if not isinstance(part, int):
                    raise PathAccessError(
                        f"Cannot use non-integer key '{part}' to index list "
                        f"at path '{'.'.join(traversed[:-1])}'"
                    )
                if part < 0 or part >= len(current):
                    raise PathAccessError(
                        f"Index {part} out of range (length={len(current)}) "
                        f"at path '{'.'.join(traversed[:-1])}'"
                    )
                current = current[part]
            else:
                raise PathAccessError(
                    f"Cannot traverse into {type(current).__name__} "
                    f"at path '{'.'.join(traversed[:-1])}'"
                )
        except (KeyError, IndexError, TypeError) as e:
            raise PathAccessError(
                f"Failed to access path '{'.'.join(traversed)}': {e}"
            ) from e

    return current


def format_value(value: Any, max_depth: int = 3, max_items: int = 10) -> str:
    """Format a value for display, with truncation for large structures.

    Args:
        value: The value to format.
        max_depth: Maximum nesting depth to show.
        max_items: Maximum items to show in lists/dicts.

    Returns:
        A formatted string representation.
    """
    import json

    def truncate(obj, depth=0):
        if depth >= max_depth:
            if isinstance(obj, dict):
                return f"{{...{len(obj)} items}}"
            elif isinstance(obj, (list, tuple)):
                return f"[...{len(obj)} items]"
            return obj

        if isinstance(obj, dict):
            if len(obj) > max_items:
                items = list(obj.items())[:max_items]
                result = {k: truncate(v, depth + 1) for k, v in items}
                result["..."] = f"({len(obj) - max_items} more)"
                return result
            return {k: truncate(v, depth + 1) for k, v in obj.items()}

        elif isinstance(obj, (list, tuple)):
            if len(obj) > max_items:
                items = [truncate(x, depth + 1) for x in obj[:max_items]]
                items.append(f"...({len(obj) - max_items} more)")
                return items
            return [truncate(x, depth + 1) for x in obj]

        return obj

    truncated = truncate(value)
    return json.dumps(truncated, indent=2, default=str)
