#!/bin/bash
################################################################################
# Background Model Check Wrapper
# Usage: ./start_background.sh [run_model_check.sh options]
# Example: ./start_background.sh -s MC.tla -c MC.cfg -d /path/to/spec
################################################################################

# Default to current directory if not specified
WORK_DIR=$(pwd)
LOG_FILE="nohup.out"

# Extract working directory if -d is passed (custom flag for this wrapper)
# We need to manually parse arguments to find -d or output override
ARGS=("$@")
PASSTHROUGH_ARGS=()

while [[ $# -gt 0 ]]; do
    key="$1"
    case $key in
        -d|--dir)
            WORK_DIR="$2"
            shift 2
            ;;
        -o|--output)
            LOG_FILE="$2"
            PASSTHROUGH_ARGS+=("$1" "$2")
            shift 2
            ;;
        *)
            PASSTHROUGH_ARGS+=("$1")
            shift
            ;;
    esac
done

# Resolve absolute path for script
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
RUN_SCRIPT="$SCRIPT_DIR/run_model_check.sh"

if [ ! -d "$WORK_DIR" ]; then
    echo "Error: Directory $WORK_DIR does not exist."
    exit 1
fi

echo "Starting model check in background..."
echo "Working Directory: $WORK_DIR"
echo "Log File:          $WORK_DIR/$LOG_FILE"
echo "Arguments:         ${PASSTHROUGH_ARGS[*]}"

# Start background process
# We cd to WORK_DIR so relative paths for spec/config work
cd "$WORK_DIR"
nohup "$RUN_SCRIPT" "${PASSTHROUGH_ARGS[@]}" > "$LOG_FILE" 2>&1 &
PID=$!

echo ""
echo "✓ Process started! PID: $PID"
echo "  To monitor:  tail -f $WORK_DIR/$LOG_FILE"
echo "  To stop:     kill $PID"
