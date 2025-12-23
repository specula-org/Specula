#!/bin/bash
################################################################################
# Generic Model Check Script
# Usage: ./run_model_check.sh -s SPEC_FILE -c CONFIG_FILE [options]
################################################################################

# Default Defaults
MEMORY="50G"
WORKERS="auto"
TIMEOUT_MINUTES=180
MAX_DEPTH=0
CHECKPOINT_MINUTES=10
LOG_FILE=""
SPEC_FILE=""
CONFIG_FILE=""

# Help function
usage() {
    echo "Usage: $0 -s SPEC_FILE -c CONFIG_FILE [options]"
    echo "Options:"
    echo "  -s FILE    Spec file (.tla)"
    echo "  -c FILE    Config file (.cfg)"
    echo "  -m MEM     Memory limit (default: 50G)"
    echo "  -w NUM     Workers (default: auto)"
    echo "  -t MIN     Timeout in minutes (default: 180)"
    echo "  -d NUM     Max depth (default: 0, no limit)"
    echo "  -k MIN     Checkpoint interval (default: 10)"
    echo "  -o FILE    Output log file (default: generated timestamp)"
    echo "  -h         Show this help"
    exit 1
}

# Parse arguments
while getopts "s:c:m:w:t:d:k:o:h" opt; do
    case $opt in
        s) SPEC_FILE="$OPTARG" ;;
        c) CONFIG_FILE="$OPTARG" ;;
        m) MEMORY="$OPTARG" ;;
        w) WORKERS="$OPTARG" ;;
        t) TIMEOUT_MINUTES="$OPTARG" ;;
        d) MAX_DEPTH="$OPTARG" ;;
        k) CHECKPOINT_MINUTES="$OPTARG" ;;
        o) LOG_FILE="$OPTARG" ;;
        h) usage ;;
        *) usage ;;
    esac
done

# Validate required arguments
if [ -z "$SPEC_FILE" ] || [ -z "$CONFIG_FILE" ]; then
    echo "Error: Spec file (-s) and Config file (-c) are required."
    usage
fi

# Set default log file if not provided
if [ -z "$LOG_FILE" ]; then
    LOG_FILE="mc_$(basename "${SPEC_FILE%.*}")_$(date +%Y%m%d_%H%M%S).log"
fi

# Locate tla2tools.jar relative to this script
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
JAR_PATH="$PROJECT_ROOT/lib/tla2tools.jar"
COMMUNITY_MODULES="$PROJECT_ROOT/lib/CommunityModules-deps.jar"

if [ ! -f "$JAR_PATH" ]; then
    echo "Error: tla2tools.jar not found at $JAR_PATH"
    exit 1
fi

# Colors
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m'

echo -e "${GREEN}================================${NC}"
echo -e "${GREEN}Model Check Launch Configuration${NC}"
echo -e "${GREEN}================================${NC}"
echo "Spec File:       $SPEC_FILE"
echo "Config File:     $CONFIG_FILE"
echo "Memory Limit:    $MEMORY"
echo "Workers:         $WORKERS"
echo "Timeout:         $TIMEOUT_MINUTES minutes"
echo "Depth Limit:     $MAX_DEPTH"
echo "Checkpoint:      $CHECKPOINT_MINUTES minutes"
echo "Log File:        $LOG_FILE"
echo -e "${GREEN}================================${NC}"

# Build TLC command
TLC_CMD="java -XX:+UseParallelGC -Xmx${MEMORY} -Xms${MEMORY}"
# Add classpath
CP="$JAR_PATH"
if [ -f "$COMMUNITY_MODULES" ]; then
    CP="$CP:$COMMUNITY_MODULES"
fi
TLC_CMD="$TLC_CMD -cp $CP tlc2.TLC"

# Add arguments
if [ "$WORKERS" != "auto" ]; then
    TLC_CMD="$TLC_CMD -workers $WORKERS"
else
    TLC_CMD="$TLC_CMD -workers auto"
fi

if [ $CHECKPOINT_MINUTES -gt 0 ]; then
    TLC_CMD="$TLC_CMD -checkpoint $CHECKPOINT_MINUTES"
fi

if [ $MAX_DEPTH -gt 0 ]; then
    TLC_CMD="$TLC_CMD -depth $MAX_DEPTH"
fi

# Add timeout
if [ $TIMEOUT_MINUTES -gt 0 ]; then
    TIMEOUT_SECONDS=$((TIMEOUT_MINUTES * 60))
    # Check if timeout command exists
    if command -v timeout &> /dev/null; then
         TLC_CMD="timeout ${TIMEOUT_SECONDS}s $TLC_CMD"
    else
         echo -e "${YELLOW}Warning: 'timeout' command not found. Timeout will be ignored.${NC}"
    fi
fi

# Add spec/config (Assuming they are in current dir or paths are absolute)
TLC_CMD="$TLC_CMD -config $CONFIG_FILE $SPEC_FILE"

echo -e "${YELLOW}Executing Command:${NC}"
echo "$TLC_CMD"
echo ""

# Execute
# Note: We use eval to handle the command string correctly
eval $TLC_CMD 2>&1 | tee "$LOG_FILE"
EXIT_CODE=${PIPESTATUS[0]}

echo ""
echo -e "${GREEN}================================${NC}"
if [ $EXIT_CODE -eq 0 ]; then
    echo -e "${GREEN}✓ Model check completed, no errors found${NC}"
elif [ $EXIT_CODE -eq 124 ]; then
    echo -e "${YELLOW}⚠ Model check timed out${NC}"
elif [ $EXIT_CODE -eq 12 ]; then
    echo -e "${YELLOW}⚠ Invariant violation found!${NC}"
    echo -e "${YELLOW}Please check log: $LOG_FILE${NC}"
else
    echo -e "${YELLOW}⚠ Model check exited abnormally (exit code: $EXIT_CODE)${NC}"
fi
echo -e "${GREEN}================================${NC}"

exit $EXIT_CODE
