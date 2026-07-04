#!/usr/bin/env bash
#
# Inter-phase review agent (used by launch_pipeline.sh; off by default).
# Thin shim → Python phase framework (src/specula/phaselib.py). Same CLI
# (`<phase> <name...>`); every argument is forwarded verbatim and the exit code
# propagates via exec. The original bash implementation is in git history; the
# behavior contract is pinned in tests/characterization/ (review_*).
set -euo pipefail
SCRIPT_DIR="$(cd -P "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
exec python3 "$SCRIPT_DIR/../../src/specula/phaselib.py" review "$@"
