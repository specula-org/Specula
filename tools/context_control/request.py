#!/usr/bin/env python3
"""Pi's tool bridge to the same CI-scoped request handler as MCP."""

import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from specula.context_control import request_compaction, request_confirmation

if __name__ == "__main__":
    print(json.dumps(request_confirmation() if sys.argv[1:] == ["--confirm"] else request_compaction(sys.argv[1])))
