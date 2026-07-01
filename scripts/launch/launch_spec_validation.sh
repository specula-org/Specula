#!/usr/bin/env bash
#
# Batch launcher: spec validation + bug hunting (Phase 3), incl. --repair mode.
# Thin shim → Python phase framework (phaselib.py). Same CLI; every argument is
# forwarded verbatim and the exit code propagates via exec. The original bash
# implementation is in git history; the behavior contract is pinned in
# tests/characterization/ (dryrun_spec_validation[_repair], gate_spec_validation).
set -euo pipefail
SCRIPT_DIR="$(cd -P "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
exec python3 "$SCRIPT_DIR/phaselib.py" spec_validation "$@"
