#!/usr/bin/env bash
# Adapter: claude-code
# Capabilities: max-turns, mcp, auto-approve, background, stop-gate
#
# Thin shim through the checkout-local Specula dispatcher. This imports the
# package without exporting PYTHONPATH into Claude or any tool it starts.
set -euo pipefail
SCRIPT_DIR="$(cd -P "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
exec "$SCRIPT_DIR/../../../specula" _adapter claude-code "$@"
