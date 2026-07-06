#!/usr/bin/env bash
#
# Batch launcher: spec validation + bug hunting (Phase 3), incl. --repair mode.
# Thin shim → Python phase framework (src/specula/phaselib.py). Same CLI; every argument is
# forwarded verbatim and the exit code propagates via exec. The original bash
# implementation is in git history; the behavior is pinned by tests/unit and
# the end-to-end dry-run in tests/e2e.
set -euo pipefail
SCRIPT_DIR="$(cd -P "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
exec python3 "$SCRIPT_DIR/../../src/specula/phaselib.py" spec_validation "$@"
