#!/usr/bin/env python3
"""Use Specula's unchanged output reader without installing an MCP server."""

import sys

from prepare import ensure_shared

if __name__ == "__main__":
    sys.path.insert(0, str(ensure_shared()))
    from reader.cli import main

    main()
