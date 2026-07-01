#!/usr/bin/env bash
#
# Batch launcher: trace harness generation (Phase 2.5).
# Thin shim → Python phase framework (phaselib.py). Same CLI; every argument is
# forwarded verbatim and the exit code propagates via exec. The original bash
# implementation is in git history; the behavior contract is pinned in
# tests/characterization/ (dryrun_harness_generation, gate_harness_generation).
set -euo pipefail
SCRIPT_DIR="$(cd -P "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
exec python3 "$SCRIPT_DIR/phaselib.py" harness_generation "$@"
