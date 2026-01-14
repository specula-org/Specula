"""Allow running the inv_checking_tool as a module.

Usage:
    python -m tools.inv_checking_tool <file> [options]
"""

from .src.cli import main

if __name__ == "__main__":
    main()
