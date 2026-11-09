"""Fixture native compactor: records the session it compacts and can be held mid-run.

Installed as tools/context_control/compact.py in the test specroot; the real
context runner invokes it exactly like the native compactor.
"""

import json
import os
import sys
import time
from pathlib import Path

fixture = Path(__file__).resolve().parents[2] / "scripts/launch/adapters"
state_file, receipt_file = sys.argv[1:3]
session = json.loads(Path(state_file).read_text())["session_id"]
with (fixture / "events.jsonl").open("a") as stream:
    event = {"kind": "start", "name": "compact", "phase": os.environ.get("SPECULA_PHASE"), "session": session}
    stream.write(json.dumps({**event, "time": time.time()}) + "\n")
receipt = Path(receipt_file)
if (fixture / "block-compact").exists():
    receipt.write_text('{"status": "comp')  # what a crash in the middle of the write leaves
    reached = fixture / "reached-compact.json"
    reached.with_name(".reached-compact.tmp").write_text(json.dumps({"pid": os.getpid(), "pgid": os.getpgrp()}))
    reached.with_name(".reached-compact.tmp").replace(reached)
    while not (fixture / "release-compact").exists():
        time.sleep(0.02)
receipt.write_text(json.dumps({"status": "completed", "evidence": {"fixture": True}}))
