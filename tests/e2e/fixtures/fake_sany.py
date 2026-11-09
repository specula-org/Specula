"""Fake ``java`` that answers ``tla2sany.SANY <module>`` like SANY and never starts a JVM.

A module parses unless it contains the marker ``SANY-ERROR`` (a parse error,
exit 255) or ``SANY-SEMANTIC`` (a semantic error reported with exit 0, as some
SANY releases do). Each call is appended to ``$FIXTURE_SANY_LOG`` when that is
set. Any other ``java`` invocation fails, so an unexpected caller is visible.
"""

import json
import os
import sys
from pathlib import Path

args = sys.argv[1:]
if "tla2sany.SANY" not in args or not args or args[-1] == "tla2sany.SANY":
    print(f"fake java: unsupported invocation {args}", file=sys.stderr)
    sys.exit(2)
module = Path(args[-1])
log = os.environ.get("FIXTURE_SANY_LOG")
if log:
    with open(log, "a") as stream:
        stream.write(json.dumps({"cwd": os.getcwd(), "module": str(module), "args": args}) + "\n")
print("\n****** SANY2 Version 2.2 created 08 July 2020\n")
print(f"Parsing file {module.resolve()}")
if "SANY-ERROR" in module.read_text(errors="replace"):
    print('***Parse Error***\nEncountered "SANY-ERROR" at line 1, column 1\n')
    print(f"Fatal errors while parsing TLA+ spec in file {module.stem}")
    sys.exit(255)
print(f"Semantic processing of module {module.stem}")
if "SANY-SEMANTIC" in module.read_text(errors="replace"):
    print("Semantic errors:\n\n*** Errors: 1\n\nline 3, col 9 to line 3, col 9 of module X\n\nUnknown operator: `y'.\n")
