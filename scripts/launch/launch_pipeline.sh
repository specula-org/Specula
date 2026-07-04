#!/usr/bin/env bash
#
# Full Specula pipeline: Code Analysis → Spec Generation → Harness Generation → Validation + Bug Hunting.
# Thin shim → Python pipeline orchestrator (src/specula/pipelinelib.py). Same CLI; every
# argument is forwarded verbatim and the exit code propagates via exec. The
# original bash implementation is in git history; the behavior contract is
# pinned in tests/characterization/ (pipeline_* / repair_* / quota_* cases).
set -euo pipefail
SCRIPT_DIR="$(cd -P "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
exec python3 "$SCRIPT_DIR/../../src/specula/pipelinelib.py" "$@"
