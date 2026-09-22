#!/usr/bin/env bash
# Run one Agent through the complete incremental-modeling skill.
set -euo pipefail
SCRIPT_DIR="$(cd -P "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
exec python3 "$SCRIPT_DIR/../../src/specula/phaselib.py" incremental "$@"
