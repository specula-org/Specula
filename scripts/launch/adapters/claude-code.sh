#!/usr/bin/env bash
# Adapter: claude-code
# Capabilities: max-turns, mcp, auto-approve, background
#
# Thin shim → Python port (src/specula/adapters/claude_code.py). Forwards args
# verbatim; exit code (incl. 75 on rate limit) propagates via exec. Behavior
# pinned in tests/characterization/. Original bash impl is in git history.
#
# Invoked by file path, NOT `python3 -m specula...`: -m would require exporting
# PYTHONPATH=src, which the spawned claude session inherits (every python the
# agent then runs inside the target repo would resolve `import specula` — and
# anything else under src/ — to this repo first), and -m puts the caller's CWD
# ahead of stdlib on sys.path (the pipeline runs from the analyzed repo, so a
# top-level json.py there would shadow `import json` inside the adapter). Path
# invocation pins sys.path[0] to the adapter's own directory and touches no env.
# Stdlib-only; runs under any python3 >= 3.10 (PEP 604 unions), no install or
# active venv needed.
set -euo pipefail
SCRIPT_DIR="$(cd -P "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
exec python3 "$SCRIPT_DIR/../../../src/specula/adapters/claude_code.py" "$@"
