#!/usr/bin/env bash
#
# Batch launcher: bug confirmation + reproduction (Phase 4a), incl. --recheck mode.
# Thin shim → Python phase framework (src/specula/phaselib.py). Same CLI; every argument is
# forwarded verbatim and the exit code propagates via exec. The original bash
# implementation is in git history; the behavior contract is pinned in
# tests/characterization/ (dryrun_bug_confirmation[_recheck], gate_bug_confirmation).
set -euo pipefail
SCRIPT_DIR="$(cd -P "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
exec python3 "$SCRIPT_DIR/../../src/specula/phaselib.py" bug_confirmation "$@"
