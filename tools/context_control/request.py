#!/usr/bin/env python3
"""Pi's tool bridge to the same CI-scoped request handler as MCP."""

import json
import os
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from specula.context_control import request_compaction, request_confirmation

if __name__ == "__main__":
    try:
        result = request_confirmation() if sys.argv[1:] == ["--confirm"] else request_compaction(sys.argv[1])
    except ValueError as exc:
        if os.environ.get("SPECULA_PHASE") != "main":
            raise  # the incremental CI workflow keeps its original failure output
        # Refused without writing a request: report why, as the MCP tool's error does.
        print(json.dumps({"status": "refused", "reason": str(exc)}))
        print(exc, file=sys.stderr)
        raise SystemExit(1) from None
    print(json.dumps(result))
