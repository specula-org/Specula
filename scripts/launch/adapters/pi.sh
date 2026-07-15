#!/usr/bin/env bash
set -euo pipefail
SCRIPT_DIR="$(cd -P "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
exec python3 "$SCRIPT_DIR/../../../src/specula/adapters/pi.py" "$@"
