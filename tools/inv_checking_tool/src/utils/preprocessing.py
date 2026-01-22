"""Preprocessing utilities for TLC output files."""

import re
from typing import Optional, Tuple


# Pattern to match ANSI escape codes
ANSI_ESCAPE_PATTERN = re.compile(r'\x1B(?:[@-Z\\-_]|\[[0-?]*[ -/]*[@-~])')

# TLC output can have different formats for invariant violation:
# - "Error: Invariant X is violated" (TLC raw output)
# - "Invariant X is violated." (TLC tool mode output)
INVARIANT_VIOLATION_PATTERN = re.compile(r"(?:Error:\s*)?Invariant\s+(\S+)\s+is violated")
PROPERTY_VIOLATION_PATTERN = re.compile(r"(?:Error:\s*)?Temporal property\s+(.+?)\s+is violated")


def strip_ansi_codes(text: str) -> str:
    """Remove ANSI escape codes from text.

    Args:
        text: Input text possibly containing ANSI codes.

    Returns:
        Text with all ANSI escape codes removed.
    """
    return ANSI_ESCAPE_PATTERN.sub('', text)


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


def extract_counterexample_path(content: str) -> Optional[str]:
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
    The metadata contains violation info, statistics, and counterexample path.

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

    # Counterexample path if present
    counterexample_path = extract_counterexample_path(content)
    if counterexample_path:
        metadata["counterexample_path"] = counterexample_path

    return content, metadata
