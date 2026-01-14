"""Preprocessing utilities for TLC output files.

This module handles various input formats including:
- Raw TLC output (starting with @!)
- Wrapped TLC output (with script headers, ANSI codes, etc.)
- Direct trace files (starting with --)
"""

import re
import io
from typing import Optional, Tuple


# Pattern to match ANSI escape codes
ANSI_ESCAPE_PATTERN = re.compile(r'\x1B(?:[@-Z\\-_]|\[[0-?]*[ -/]*[@-~])')

# Markers for identifying TLC output sections
ERROR_BEHAVIOR_MARKER = "The behavior up to this point is:"
INVARIANT_VIOLATION_PATTERN = re.compile(r"Error:\s*Invariant\s+(\S+)\s+is violated")
PROPERTY_VIOLATION_PATTERN = re.compile(r"Error:\s*Temporal property\s+(.+?)\s+is violated")
STATE_PATTERN = re.compile(r"^State\s+(\d+):\s*<(.+?)>")
END_MARKERS = [
    "The number of states generated",
    "Progress:",
    "Finished in",
    "Worker: rmi",
]


def strip_ansi_codes(text: str) -> str:
    """Remove ANSI escape codes from text.

    Args:
        text: Input text possibly containing ANSI codes.

    Returns:
        Text with all ANSI escape codes removed.
    """
    return ANSI_ESCAPE_PATTERN.sub('', text)


def find_trace_start(content: str) -> Optional[int]:
    """Find the starting position of the error trace in TLC output.

    Args:
        content: The TLC output content.

    Returns:
        The character position where the trace starts, or None if not found.
    """
    # Look for the behavior marker
    marker_pos = content.find(ERROR_BEHAVIOR_MARKER)
    if marker_pos == -1:
        return None

    # Find the start of the line containing "Error:"
    # Go backwards to find the "Error: Invariant..." line
    search_start = max(0, marker_pos - 200)
    error_match = INVARIANT_VIOLATION_PATTERN.search(content[search_start:marker_pos + len(ERROR_BEHAVIOR_MARKER)])
    if error_match:
        return search_start + error_match.start()

    # Try property violation pattern
    error_match = PROPERTY_VIOLATION_PATTERN.search(content[search_start:marker_pos + len(ERROR_BEHAVIOR_MARKER)])
    if error_match:
        return search_start + error_match.start()

    # Fallback: just return the marker position's line start
    line_start = content.rfind('\n', 0, marker_pos)
    return line_start + 1 if line_start != -1 else 0


def find_trace_end(content: str, start_pos: int) -> int:
    """Find the ending position of the error trace.

    The trace ends after the last state variable, but we need to include
    the end marker line so that get_out_converted_string can properly
    terminate the trace.

    Args:
        content: The TLC output content.
        start_pos: The starting position of the trace.

    Returns:
        The character position where the trace ends (inclusive of end marker).
    """
    search_content = content[start_pos:]

    # Find the earliest end marker
    end_pos = len(search_content)
    for marker in END_MARKERS:
        pos = search_content.find(marker)
        if pos != -1 and pos < end_pos:
            # Include this line (go to end of line, not start)
            line_end = search_content.find('\n', pos)
            if line_end != -1:
                end_pos = line_end + 1  # Include the newline
            else:
                end_pos = len(search_content)  # End of content

    return start_pos + end_pos


def extract_violation_info(content: str) -> Tuple[Optional[str], Optional[str]]:
    """Extract the violated invariant/property name from TLC output.

    Args:
        content: The TLC output content.

    Returns:
        A tuple of (violation_type, violation_name).
        violation_type is either "invariant" or "property".
    """
    # Try invariant violation
    match = INVARIANT_VIOLATION_PATTERN.search(content)
    if match:
        return ("invariant", match.group(1))

    # Try temporal property violation
    match = PROPERTY_VIOLATION_PATTERN.search(content)
    if match:
        return ("property", match.group(1))

    return (None, None)


def extract_statistics(content: str) -> dict:
    """Extract TLC statistics from the output.

    Args:
        content: The TLC output content.

    Returns:
        A dictionary containing statistics like states generated, time, etc.
    """
    stats = {}

    # States generated
    match = re.search(r"The number of states generated:\s*(\d+)", content)
    if match:
        stats["states_generated"] = int(match.group(1))

    # Simulation seed
    match = re.search(r"Simulation using seed\s+(-?\d+)", content)
    if match:
        stats["simulation_seed"] = int(match.group(1))

    # Progress info
    match = re.search(r"Progress:\s*(\d+)\s*states checked", content)
    if match:
        stats["states_checked"] = int(match.group(1))

    # Traces generated
    match = re.search(r"(\d+)\s*traces generated", content)
    if match:
        stats["traces_generated"] = int(match.group(1))

    # Finished time
    match = re.search(r"Finished in\s+(.+?)\s+at", content)
    if match:
        stats["duration"] = match.group(1)

    return stats


def preprocess_tlc_output(file_path: str) -> Tuple[str, dict]:
    """Preprocess a TLC output file for parsing.

    This function handles various input formats:
    - Raw TLC output
    - Wrapped output with ANSI codes and script headers
    - Direct trace files

    Args:
        file_path: Path to the TLC output file.

    Returns:
        A tuple of (preprocessed_content, metadata).
        The preprocessed content is ready for TraceReader.
        The metadata contains violation info and statistics.

    Raises:
        FileNotFoundError: If the file does not exist.
        ValueError: If the file does not contain a valid TLC trace.
    """
    with open(file_path, 'r', encoding='utf-8', errors='replace') as f:
        content = f.read()

    # Strip ANSI codes
    content = strip_ansi_codes(content)

    # Extract metadata before processing
    metadata = {}

    # Get violation info
    violation_type, violation_name = extract_violation_info(content)
    if violation_name:
        metadata["violation_type"] = violation_type
        metadata["violation_name"] = violation_name

    # Get statistics
    metadata["statistics"] = extract_statistics(content)

    # Check if this is already a trace file (starts with --)
    if content.lstrip().startswith("--"):
        return content, metadata

    # Check if this starts with @! (raw TLC output)
    if content.lstrip().startswith("@!"):
        # Add a dummy line for the converter
        return "PLACEHOLDER\n" + content, metadata

    # Find the trace section
    trace_start = find_trace_start(content)
    if trace_start is None:
        raise ValueError(
            "Could not find error trace in TLC output. "
            "Expected 'The behavior up to this point is:' marker."
        )

    trace_end = find_trace_end(content, trace_start)
    trace_content = content[trace_start:trace_end]

    # Add a placeholder line to make the converter work
    # The converter expects a non-@ first line to trigger error mode
    return "PLACEHOLDER\n" + trace_content, metadata


def convert_to_trace_format(content: str) -> str:
    """Convert preprocessed content to TLA+ trace format.

    This function uses TraceReader's get_out_converted_string to convert
    TLC output format to the standard trace format that can be parsed.

    Args:
        content: Preprocessed TLC output content.

    Returns:
        Content in TLA+ trace format (starting with --).
    """
    # Import here to avoid circular imports
    from ..trace_reader import TraceReader

    # If already in trace format, return as-is
    if content.lstrip().startswith("--"):
        return content

    # Convert using TraceReader's utility
    f = io.StringIO(content)
    converted_lines = list(TraceReader.get_out_converted_string(f))

    if not converted_lines:
        raise ValueError("Failed to convert TLC output to trace format.")

    return ''.join(converted_lines)
