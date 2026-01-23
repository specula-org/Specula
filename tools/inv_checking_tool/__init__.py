"""TLC Model Checking Output Analysis Tools.

This package provides tools for parsing and analyzing TLC model checker output,
making it easier for agents and users to debug invariant violations.

Example usage:
    from tools.inv_checking_tool import TLCOutputReader

    reader = TLCOutputReader("path/to/tlc_output.log")
    summary = reader.get_summary()
    print(f"Violated: {summary.violation_name}")
"""

from .src.tlc_output_reader import TLCOutputReader

__all__ = ["TLCOutputReader"]
