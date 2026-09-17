#!/usr/bin/env bash
set -euo pipefail
SCRIPT_DIR="$(cd -P "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
export PYTHONPATH="$SCRIPT_DIR/../../src${PYTHONPATH:+:$PYTHONPATH}"
exec python3 -m specula.ci_result "$@"
