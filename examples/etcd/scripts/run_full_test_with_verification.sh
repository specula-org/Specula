#!/bin/bash

# Specula ETCD Example - Complete Workflow with TLA+ Verification
# This script demonstrates the complete workflow including trace conversion and verification

set -e

echo "=== Specula ETCD Complete Workflow with TLA+ Verification ==="
echo

# Get directories
SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
PROJECT_ROOT="$( cd "$SCRIPT_DIR/../../.." &> /dev/null && pwd )"
EXAMPLE_DIR="$( cd "$SCRIPT_DIR/.." &> /dev/null && pwd )"
SPEC_DIR="$EXAMPLE_DIR/spec/step5/spec"

echo "Project root: $PROJECT_ROOT"
echo "Example directory: $EXAMPLE_DIR"
echo "Spec directory: $SPEC_DIR"
echo

# Step 1: Run instrumentation and generate system trace
echo "1. Running instrumentation and generating system trace..."
cd "$EXAMPLE_DIR"
bash scripts/run_instrumentation_test.sh

# Check if system trace was generated
SYSTEM_TRACE_FILE="$EXAMPLE_DIR/runners/raft_simulator/raft_trace.ndjson"
if [ ! -f "$SYSTEM_TRACE_FILE" ]; then
    echo "Error: System trace file not found: $SYSTEM_TRACE_FILE"
    exit 1
fi

echo "System trace generated: $SYSTEM_TRACE_FILE"
echo "System trace size: $(wc -l < "$SYSTEM_TRACE_FILE") lines"
echo

# Step 2: Convert system trace to TLA+ format
echo "2. Converting system trace to TLA+ format..."
TLA_TRACE_FILE="$SPEC_DIR/trace.ndjson"

python3 "$SCRIPT_DIR/trace_converter.py" \
    "$SYSTEM_TRACE_FILE" \
    "$TLA_TRACE_FILE" \
    --servers n1 n2 n3 \
    --values 1 2 3

if [ ! -f "$TLA_TRACE_FILE" ]; then
    echo "Error: TLA+ trace file not created: $TLA_TRACE_FILE"
    exit 1
fi

echo "TLA+ trace generated: $TLA_TRACE_FILE"
echo "TLA+ trace size: $(wc -l < "$TLA_TRACE_FILE") lines"
echo

# Step 3: Show sample of converted trace
echo "3. Sample of converted TLA+ trace:"
head -5 "$TLA_TRACE_FILE"
echo

# Step 4: Run TLA+ model checking
echo "4. Running TLA+ model checking..."
cd "$SPEC_DIR"

# Check if TLA+ tools are available
TLA_TOOLS_JAR="$PROJECT_ROOT/lib/tla2tools.jar"
if [ ! -f "$TLA_TOOLS_JAR" ]; then
    echo "Error: TLA+ tools not found: $TLA_TOOLS_JAR"
    exit 1
fi

# Set environment variable for trace path
export TRACE_PATH="$TLA_TRACE_FILE"

echo "Using trace file: $TRACE_PATH"
echo "Running TLA+ model checker..."

# Run TLC with trace specification
java -cp "$TLA_TOOLS_JAR" tlc2.TLC \
    -config specTrace.cfg \
    specTrace.tla \
    -deadlock \
    -workers auto \
    2>&1 | tee tlc_output.log

# Check TLC result
if grep -q "Model checking completed" tlc_output.log; then
    echo "✓ TLA+ model checking completed successfully"
    TLC_SUCCESS=true
else
    echo "✗ TLA+ model checking failed or incomplete"
    TLC_SUCCESS=false
fi

# Step 5: Analysis and summary
echo
echo "5. Analysis and Summary"
echo "======================"

# System trace analysis
SYSTEM_EVENTS=$(grep -c "action" "$SYSTEM_TRACE_FILE" || echo "0")
echo "System events captured: $SYSTEM_EVENTS"

# TLA+ trace analysis  
TLA_EVENTS=$(tail -n +2 "$TLA_TRACE_FILE" | wc -l)  # Skip config line
echo "TLA+ events generated: $TLA_EVENTS"

# Event type breakdown
echo "Event type breakdown:"
grep '"event"' "$TLA_TRACE_FILE" | sort | uniq -c | while read count event; do
    echo "  $event: $count times"
done

# TLC output analysis
if [ -f tlc_output.log ]; then
    echo
    echo "TLC Model Checking Results:"
    if grep -q "Error:" tlc_output.log; then
        echo "  ✗ Errors found:"
        grep "Error:" tlc_output.log | head -3
    else
        echo "  ✓ No errors found"
    fi
    
    if grep -q "states generated" tlc_output.log; then
        STATES_GENERATED=$(grep "states generated" tlc_output.log | tail -1)
        echo "  States: $STATES_GENERATED"
    fi
fi

echo
echo "=== Complete Workflow Summary ==="
echo "✓ Step 1: Instrumentation completed"
echo "✓ Step 2: System trace generated ($SYSTEM_EVENTS events)"
echo "✓ Step 3: Trace converted to TLA+ format ($TLA_EVENTS events)"
if [ "$TLC_SUCCESS" = true ]; then
    echo "✓ Step 4: TLA+ verification passed"
else
    echo "✗ Step 4: TLA+ verification failed"
fi

echo
echo "Generated files:"
echo "  - Instrumented code: $EXAMPLE_DIR/output/instrumented_raft.go"
echo "  - System trace: $SYSTEM_TRACE_FILE"
echo "  - TLA+ trace: $TLA_TRACE_FILE"
echo "  - TLC output: $SPEC_DIR/tlc_output.log"

echo
echo "Next steps:"
echo "1. Analyze TLC output for any specification violations"
echo "2. Refine instrumentation if needed"
echo "3. Extend trace conversion for more complex scenarios"
echo "4. Use traces for debugging and verification"

if [ "$TLC_SUCCESS" = true ]; then
    exit 0
else
    exit 1
fi 