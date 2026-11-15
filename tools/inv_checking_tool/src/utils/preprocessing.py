"""Preprocessing utilities for TLC output files.

This module handles various input formats including:
- Raw TLC output (starting with @!)
- Wrapped TLC output (with script headers, ANSI codes, etc.)
- Direct trace files (starting with --)
- JSON trace files (from -dumptrace json)
"""

import io
import re

# Pattern to match ANSI escape codes
ANSI_ESCAPE_PATTERN = re.compile(r"\x1B(?:[@-Z\\-_]|\[[0-?]*[ -/]*[@-~])")

# Markers that introduce a TLC error trace. Invariant, action-property, and deadlock
# violations print the first; liveness (temporal property) violations print the second.
ERROR_BEHAVIOR_MARKER = "The behavior up to this point is:"
LIVENESS_BEHAVIOR_MARKER = "The following behavior constitutes a counter-example:"
ERROR_BEHAVIOR_MARKERS = (ERROR_BEHAVIOR_MARKER, LIVENESS_BEHAVIOR_MARKER)

# TLC prints violations with an "Error: " prefix in raw output and without it in tool mode.
# Each entry is (violation_type, pattern); group 1, when present, is the violated name.
# TLC does not say which temporal property failed when a liveness check fails.
VIOLATION_PATTERNS = (
    ("invariant", re.compile(r"(?:Error:\s*)?Invariant\s+(\S+)\s+is violated")),
    ("action_property", re.compile(r"(?:Error:\s*)?Action property\s+(\S+)\s+is violated")),
    ("temporal_property", re.compile(r"^(?:Error:\s*)?Property\s+(\S+)\s+is violated by the initial state", re.M)),
    ("temporal_property", re.compile(r"^(?:Error:\s*)?Temporal properties were violated\.", re.M)),
    ("deadlock", re.compile(r"^(?:Error:\s*)?Deadlock reached\.", re.M)),
)

# A liveness counterexample is a lasso: the printed states followed by a loop. TLC closes it
# with "Back to state N[: <action>]" ("N: Back to state[: <action>]" in tool mode), or with
# "State N: Stuttering" ("N: Stuttering" in tool mode) when the behavior stays in the last
# printed state forever.
BACK_TO_STATE_PATTERN = re.compile(r"^(?:Back to state (\d+)|(\d+): Back to state)(?::\s*(.*?))?\s*$", re.M)
STUTTERING_PATTERN = re.compile(r"^(?:State )?(\d+):\s*Stuttering\s*$", re.M)


def strip_ansi_codes(text: str) -> str:
    """Remove ANSI escape codes from text.

    Args:
        text: Input text possibly containing ANSI codes.

    Returns:
        Text with all ANSI escape codes removed.
    """
    return ANSI_ESCAPE_PATTERN.sub("", text)


def extract_violation_info(content: str) -> tuple[str | None, str | None]:
    """Extract the kind of violation and the violated name from TLC output.

    Args:
        content: The TLC output content.

    Returns:
        A tuple of (violation_type, violation_name). violation_type is one of
        "invariant", "action_property", "temporal_property", or "deadlock".
        violation_name is None when TLC does not report a name, which is the
        case for deadlocks and for liveness violations found after the initial state.
    """
    for violation_type, pattern in VIOLATION_PATTERNS:
        match = pattern.search(content)
        if match:
            name = match.group(1) if pattern.groups else None
            return (violation_type, name)

    return (None, None)


def has_error_trace(content: str) -> bool:
    """Return whether the TLC output contains a printed error trace."""
    return any(marker in content for marker in ERROR_BEHAVIOR_MARKERS)


def extract_lasso_info(content: str) -> dict | None:
    """Describe the loop that closes a liveness counterexample in TLC text output.

    Returns:
        None when the output has no liveness counterexample. Otherwise a dict with:
        - kind: "back_to_state" (the behavior returns to an earlier state and repeats
          from there) or "stuttering" (the behavior takes no further step).
        - loop_start: 1-indexed state where the repeating suffix begins; for
          stuttering, the last printed state.
        - action: the step that closes the loop, or None for stuttering.
    """
    start = content.find(LIVENESS_BEHAVIOR_MARKER)
    if start < 0:
        return None
    trace = content[start:]

    match = STUTTERING_PATTERN.search(trace)
    if match:
        return {"kind": "stuttering", "loop_start": int(match.group(1)) - 1, "action": None}

    match = BACK_TO_STATE_PATTERN.search(trace)
    if match:
        return {
            "kind": "back_to_state",
            "loop_start": int(match.group(1) or match.group(2)),
            "action": match.group(3) or None,
        }

    return None


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


def extract_counterexample_path(content: str) -> str | None:
    """Extract the counterexample file path from TLC output."""
    match = None
    for line in content.splitlines():
        if "CounterExample written:" in line:
            line = line.strip().strip('"')
            _, _, path = line.partition("CounterExample written:")
            path = path.strip()
            if path:
                match = path
    return match


def preprocess_tlc_output(file_path: str) -> tuple[str, dict]:
    """Preprocess a TLC output file for parsing.

    This function handles various input formats:
    - Raw TLC output
    - Wrapped output with ANSI codes and script headers
    - Direct trace files

    Args:
        file_path: Path to the TLC output file.

    Returns:
        A tuple of (preprocessed_content, metadata).
    The metadata contains violation info, statistics, and counterexample path.

    Raises:
        FileNotFoundError: If the file does not exist.
        ValueError: If the file does not contain a valid TLC trace.
    """
    with open(file_path, encoding="utf-8", errors="replace") as f:
        content = f.read()

    # Strip ANSI codes
    content = strip_ansi_codes(content)

    # Extract metadata before processing
    metadata = {}

    # Get violation info
    violation_type, violation_name = extract_violation_info(content)
    if violation_type:
        metadata["violation_type"] = violation_type
        metadata["violation_name"] = violation_name

    lasso = extract_lasso_info(content)
    if lasso:
        metadata["lasso"] = lasso

    # Get statistics
    metadata["statistics"] = extract_statistics(content)

    # Counterexample path if present
    counterexample_path = extract_counterexample_path(content)
    if counterexample_path:
        metadata["counterexample_path"] = counterexample_path

    return content, metadata


def convert_to_trace_format(content: str) -> str:
    """Convert preprocessed content to TLA+ trace format.

    This function uses TraceReader's get_out_converted_string to convert
    TLC output format to the standard trace format that can be parsed.

    Args:
        content: Preprocessed TLC output content.

    Returns:
        Content in TLA+ trace format (starting with --).
    """
    from ..trace_reader import TraceReader

    # If already in trace format, return as-is
    if content.lstrip().startswith("--"):
        return content

    f = io.StringIO(content)
    converted_lines = list(TraceReader.get_out_converted_string(f))

    if not converted_lines:
        raise ValueError("Failed to convert TLC output to trace format.")

    return "".join(converted_lines)
