#!/usr/bin/env bash
#
# Batch launcher: TLA+ spec generation (Phase 2).
# Thin shim → Python phase framework (src/specula/phaselib.py). Same CLI; every argument is
# forwarded verbatim and the exit code propagates via exec. The original bash
# implementation is in git history; the behavior contract is pinned in
# tests/characterization/ (dryrun_spec_generation, gate_spec_generation).
set -euo pipefail
SCRIPT_DIR="$(cd -P "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
exec python3 "$SCRIPT_DIR/../../src/specula/phaselib.py" spec_generation "$@"
