#!/usr/bin/env bash
#
# Overnight batch scheduler for Specula pipeline.
# Thin shim → Python scheduler (src/specula/schedulerlib.py). Same CLI; every argument is
# forwarded verbatim and the exit code propagates via exec. The original bash
# implementation is in git history; the behavior is pinned by
# tests/unit/test_schedulerlib.py and the batch dry-run in tests/e2e.
set -euo pipefail
SCRIPT_DIR="$(cd -P "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
exec python3 "$SCRIPT_DIR/../../src/specula/schedulerlib.py" "$@"
