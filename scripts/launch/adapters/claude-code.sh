#!/usr/bin/env bash
# Adapter: claude-code
# Capabilities: max-turns, mcp, auto-approve, background, stop-gate
#
# Thin shim to the internal console command installed with Specula. This keeps
# package resolution in the installation and does not export PYTHONPATH into
# Claude or any tool it starts.
set -euo pipefail
exec specula-adapter claude-code "$@"
