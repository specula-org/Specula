#!/usr/bin/env bash
# Run one continuous main session per target (analysis through validation).
set -euo pipefail
SCRIPT_DIR="$(cd -P "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
exec python3 "$SCRIPT_DIR/../../src/specula/phaselib.py" main "$@"
