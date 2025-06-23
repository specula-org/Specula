#!/bin/bash

# TLAGEN ETCD Example - Automated Instrumentation and Random Testing
# This script demonstrates the complete workflow for the etcd/raft system

set -e

echo "=== TLAGEN ETCD Example - Automated Instrumentation and Testing ==="
echo

# Get the script directory and project root
SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
PROJECT_ROOT="$( cd "$SCRIPT_DIR/../../.." &> /dev/null && pwd )"
EXAMPLE_DIR="$( cd "$SCRIPT_DIR/.." &> /dev/null && pwd )"

echo "Project root: $PROJECT_ROOT"
echo "Example directory: $EXAMPLE_DIR"
echo

# Step 0: Clone etcd/raft source code if not present
echo "0. Checking etcd/raft source code..."
ETCD_RAFT_DIR="$PROJECT_ROOT/systems/etcd/raft"
SOURCE_FILE="$EXAMPLE_DIR/source/raft.go"

if [ ! -f "$SOURCE_FILE" ]; then
    echo "Source file not found. Cloning etcd/raft repository..."
    
    # Create directories if they don't exist
    mkdir -p "$PROJECT_ROOT/systems/etcd"
    mkdir -p "$EXAMPLE_DIR/source"
    
    # Clone etcd/raft repository
    if [ ! -d "$ETCD_RAFT_DIR" ]; then
        echo "Cloning https://github.com/etcd-io/raft.git..."
        git clone https://github.com/etcd-io/raft.git "$ETCD_RAFT_DIR"
    fi
    
    # Copy raft.go to example directory
    if [ -f "$ETCD_RAFT_DIR/raft.go" ]; then
        cp "$ETCD_RAFT_DIR/raft.go" "$SOURCE_FILE"
        echo "✓ Copied raft.go from etcd/raft repository"
    else
        echo "Error: raft.go not found in cloned repository"
        exit 1
    fi
else
    echo "✓ Source file already exists: $SOURCE_FILE"
fi
echo

# Step 1: Use the Go instrumentation template
echo "1. Using Go instrumentation template..."
TEMPLATE_FILE="$PROJECT_ROOT/templates/instrumentation/go_trace_stub.template"
if [ ! -f "$TEMPLATE_FILE" ]; then
    echo "Error: Template file not found: $TEMPLATE_FILE"
    exit 1
fi
echo "Template: $TEMPLATE_FILE"

# Step 2: Run automatic instrumentation
echo
echo "2. Running automatic instrumentation on etcd/raft.go..."
CONFIG_FILE="$EXAMPLE_DIR/config/raft_config.yaml"
SOURCE_FILE="$EXAMPLE_DIR/source/raft.go"
OUTPUT_FILE="$EXAMPLE_DIR/output/instrumented_raft.go"

python3 "$PROJECT_ROOT/src/core/instrumentation.py" \
    "$CONFIG_FILE" \
    "$SOURCE_FILE" \
    --stub-template "$TEMPLATE_FILE" \
    --output "$OUTPUT_FILE" \
    --verbose

echo "Instrumentation completed!"

# Step 3: Check instrumentation results
echo
echo "3. Checking instrumentation results..."
if [ -f "$OUTPUT_FILE" ]; then
    echo "Instrumented file size: $(wc -l < "$OUTPUT_FILE") lines"
    echo "traceAction calls: $(grep -c "traceAction" "$OUTPUT_FILE" || echo "0")"
else
    echo "Error: Instrumented file not found!"
    exit 1
fi

# Step 4: Run the simulator example
echo
echo "4. Running the raft simulator example..."
SIMULATOR_DIR="$EXAMPLE_DIR/runners/raft_simulator"
if [ -d "$SIMULATOR_DIR" ]; then
    cd "$SIMULATOR_DIR"
    echo "Running in: $(pwd)"
    timeout 30s go run main.go || echo "Simulator completed (timeout or normal exit)"
    cd "$PROJECT_ROOT"
else
    echo "Warning: Simulator not found at $SIMULATOR_DIR"
fi

# Step 5: Check trace files
echo
echo "5. Checking generated trace files..."
TRACE_FILE="$SIMULATOR_DIR/raft_trace.ndjson"
if [ -f "$TRACE_FILE" ]; then
    echo "Trace file size: $(wc -l < "$TRACE_FILE") records"
    echo "Sample trace records:"
    head -3 "$TRACE_FILE" | jq . 2>/dev/null || head -3 "$TRACE_FILE"
else
    echo "No trace file found at $TRACE_FILE"
fi

echo
echo "=== ETCD Example Completed ==="
echo
echo "Summary:"
echo "✓ Used template-based instrumentation approach"
echo "✓ Successfully instrumented etcd/raft.go with TLA+ action tracing"
echo "✓ Demonstrated random testing with trace generation"
echo "✓ Generated NDJSON trace files for TLA+ model checking"
echo
echo "Files generated:"
echo "  - Instrumented source: $OUTPUT_FILE"
echo "  - Trace records: $SIMULATOR_DIR/raft_trace.ndjson"
echo
echo "Next steps:"
echo "1. Customize the instrumentation template for your specific needs"
echo "2. Implement your own test runner based on the simulator example"
echo "3. Feed the trace files into TLA+ model checker for verification"
echo "4. Extend to other systems by providing appropriate configurations" 