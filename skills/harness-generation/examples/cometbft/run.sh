#!/bin/bash
# Run CometBFT consensus trace harness.
# Generates NDJSON traces for TLA+ trace validation.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
COMETBFT_DIR="$SCRIPT_DIR/../artifact/cometbft"
TRACE_DIR="$SCRIPT_DIR/../traces"

mkdir -p "$TRACE_DIR"

export TRACE_DIR
export PATH=/usr/local/go/bin:$HOME/go/bin:/usr/bin:$PATH

echo "==> Running CometBFT trace scenarios..."
cd "$COMETBFT_DIR"

# Run each scenario test
for scenario in BasicConsensus TimeoutPropose LockAndRelock TwoHeights; do
    echo "--- Scenario: $scenario"
    if go test -v -run "TestScenario${scenario}" -timeout 120s ./consensus/ 2>&1; then
        echo "PASS: $scenario"
    else
        echo "FAIL: $scenario"
    fi
done

echo ""
echo "==> Traces written to: $TRACE_DIR"
ls -la "$TRACE_DIR"/*.ndjson 2>/dev/null || echo "(no traces found)"
