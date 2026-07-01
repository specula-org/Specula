#!/usr/bin/env bash
#
# Batch launcher: bug severity classification (Phase 4b).
# Thin shim → Python phase framework (phaselib.py). Same CLI; every argument is
# forwarded verbatim and the exit code propagates via exec. The original bash
# implementation is in git history; the behavior contract is pinned in
# tests/characterization/ (dryrun_bug_classification, gate_bug_classification).
set -euo pipefail
SCRIPT_DIR="$(cd -P "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
exec python3 "$SCRIPT_DIR/phaselib.py" bug_classification "$@"
