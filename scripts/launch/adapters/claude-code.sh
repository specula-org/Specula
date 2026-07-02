#!/usr/bin/env bash
# Adapter: claude-code
# Capabilities: max-turns, mcp, auto-approve, background
#
# Thin shim → Python port (specula.adapters.claude_code). Forwards args verbatim;
# exit code (incl. 75 on rate limit) propagates via exec. Behavior pinned in
# tests/characterization/. Original bash impl is in git history.
#
# The adapter is stdlib-only, so src/ on PYTHONPATH lets any `python3` run it —
# no install or active venv needed, so bare-environment pipeline callers work.
set -euo pipefail
SCRIPT_DIR="$(cd -P "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SPECULA_SRC="$(cd -P "$SCRIPT_DIR/../../../src" && pwd)"
export PYTHONPATH="$SPECULA_SRC${PYTHONPATH:+:$PYTHONPATH}"
exec python3 -m specula.adapters.claude_code "$@"
