#!/usr/bin/env bash
# Trusted GitHub event entrypoint; verification stays in launch_pipeline.sh.
set -euo pipefail
SCRIPT_DIR="$(cd -P "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
exec python3 "$SCRIPT_DIR/../../src/specular/github_ci.py" "$@"
