#!/usr/bin/env bash
# Adapter: claude-code
# Capabilities: max-turns, mcp, auto-approve, background
#
# Thin shim → Python port (claude_code.py). Same CLI contract as before; every
# argument is forwarded verbatim, and the Python process's exit code (incl. 75
# on rate limit) propagates via exec. The original bash implementation lives in
# git history; the behavior contract is pinned in tests/characterization/.
set -euo pipefail
SCRIPT_DIR="$(cd -P "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
exec python3 "$SCRIPT_DIR/claude_code.py" "$@"
