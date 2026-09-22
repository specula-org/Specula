#!/usr/bin/env python3
"""Run the selected native compactor with the installed context-tool dependencies."""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from specula.native_compaction import main

if __name__ == "__main__":
    raise SystemExit(main())
