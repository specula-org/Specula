#!/bin/bash
################################################################################
# Generic Model Check Script
# Usage: ./run_model_check.sh -s SPEC_FILE -c CONFIG_FILE [options]
################################################################################

# Default Defaults
MEMORY="50G"
OFFHEAP_MEMORY="200G"
WORKERS="auto"
TIMEOUT_MINUTES=180
MAX_DEPTH=0
CHECKPOINT_MINUTES=10
LOG_FILE=""
SPEC_FILE=""
CONFIG_FILE=""
SIMULATE_MODE=false
SIMULATE_NUM=1
SIMULATE_FILE=""
SIMULATE_DEPTH=0
DEADLOCK_CHECK=false
CONTINUE_ON_ERROR=false

# Help function
usage() {
    echo "Usage: $0 -s SPEC_FILE -c CONFIG_FILE [options]"
    echo ""
    echo "Required:"
    echo "  -s FILE    Spec file (.tla)"
    echo "  -c FILE    Config file (.cfg)"
    echo ""
    echo "General Options:"
    echo "  -m MEM     Memory limit (default: 50G)"
    echo "  -M MEM     Off-heap memory limit (default: 200G)"
    echo "  -w NUM     Workers (default: auto)"
    echo "  -t MIN     Timeout in minutes (default: 180)"
    echo "  -o FILE    Output log file (default: generated timestamp)"
    echo "  -h         Show this help"
    echo ""
    echo "Model Checking Options:"
    echo "  -d NUM     Max depth (default: 0, no limit)"
    echo "  -k MIN     Checkpoint interval (default: 10)"
    echo "  -D         Enable deadlock checking"
    echo "  -C         Continue after finding errors (find all violations)"
    echo ""
    echo "Simulation Mode Options:"
    echo "  -S         Enable simulation mode (random trace generation)"
    echo "  -n NUM     Number of traces to generate (default: 1)"
    echo "  -f FILE    Trace file prefix (default: traces/trace)"
    echo "  -p NUM     Simulation depth (default: 0, no limit)"
    echo ""
    echo "Examples:"
    echo "  # Standard model checking"
    echo "  $0 -s MC.tla -c MC.cfg -m 50G -w 80 -d 100 -D"
    echo ""
    echo "  # Model checking - continue after errors"
    echo "  $0 -s MC.tla -c MC.cfg -m 50G -w 80 -C"
    echo ""
    echo "  # Simulation mode - generate traces"
    echo "  $0 -s MC.tla -c MC.cfg -S -n 1 -f traces/trace -w 80 -D"
    exit 1
}

# Parse arguments
while getopts "s:c:m:M:w:t:d:k:o:SDCn:f:p:h" opt; do
    case $opt in
        s) SPEC_FILE="$OPTARG" ;;
        c) CONFIG_FILE="$OPTARG" ;;
        m) MEMORY="$OPTARG" ;;
        M) OFFHEAP_MEMORY="$OPTARG" ;;
        w) WORKERS="$OPTARG" ;;
        t) TIMEOUT_MINUTES="$OPTARG" ;;
        d) MAX_DEPTH="$OPTARG" ;;
        k) CHECKPOINT_MINUTES="$OPTARG" ;;
        o) LOG_FILE="$OPTARG" ;;
        S) SIMULATE_MODE=true ;;
        D) DEADLOCK_CHECK=true ;;
        C) CONTINUE_ON_ERROR=true ;;
        n) SIMULATE_NUM="$OPTARG" ;;
        f) SIMULATE_FILE="$OPTARG" ;;
        p) SIMULATE_DEPTH="$OPTARG" ;;
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
    if [ "$SIMULATE_MODE" = true ]; then
        LOG_FILE="sim_$(basename "${SPEC_FILE%.*}")_$(date +%Y%m%d_%H%M%S).log"
    else
        LOG_FILE="mc_$(basename "${SPEC_FILE%.*}")_$(date +%Y%m%d_%H%M%S).log"
    fi
fi

# Locate tla2tools.jar relative to this script
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
JAR_PATH="$PROJECT_ROOT/lib/tla2tools.jar"
COMMUNITY_MODULES="$PROJECT_ROOT/lib/CommunityModules-deps.jar"

# Check for alternative paths
if [ ! -f "$JAR_PATH" ]; then
    # Try tlc-cmd path
    if [ -f "/home/ubuntu/tlc-cmd/CommunityModules-deps.jar" ]; then
        COMMUNITY_MODULES="/home/ubuntu/tlc-cmd/CommunityModules-deps.jar"
    fi
    if [ -f "/home/ubuntu/specula/lib/tla2tools.jar" ]; then
        JAR_PATH="/home/ubuntu/specula/lib/tla2tools.jar"
    fi
fi

if [ ! -f "$JAR_PATH" ]; then
    echo "Error: tla2tools.jar not found at $JAR_PATH"
    exit 1
fi

# Colors
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

echo -e "${GREEN}================================${NC}"
if [ "$SIMULATE_MODE" = true ]; then
    echo -e "${GREEN}TLC Simulation Mode${NC}"
else
    echo -e "${GREEN}TLC Model Checking Mode${NC}"
fi
echo -e "${GREEN}================================${NC}"
echo "Spec File:       $SPEC_FILE"
echo "Config File:     $CONFIG_FILE"
echo "Memory Limit:    $MEMORY"
echo "Off-heap Memory: $OFFHEAP_MEMORY"
echo "Workers:         $WORKERS"
echo "Timeout:         $TIMEOUT_MINUTES minutes"

if [ "$SIMULATE_MODE" = true ]; then
    echo -e "${BLUE}--- Simulation Settings ---${NC}"
    echo "Trace Count:     $SIMULATE_NUM"
    if [ -n "$SIMULATE_FILE" ]; then
        echo "Trace File:      $SIMULATE_FILE"
    else
        echo "Trace File:      (not saved)"
    fi
    if [ $SIMULATE_DEPTH -gt 0 ]; then
        echo "Sim Depth:       $SIMULATE_DEPTH"
    else
        echo "Sim Depth:       (no limit)"
    fi
else
    echo -e "${BLUE}--- Model Checking Settings ---${NC}"
    echo "Depth Limit:     $MAX_DEPTH"
    echo "Checkpoint:      $CHECKPOINT_MINUTES minutes"
fi

if [ "$DEADLOCK_CHECK" = true ]; then
    echo "Deadlock Check:  enabled"
fi
if [ "$CONTINUE_ON_ERROR" = true ]; then
    echo "Continue on Error: enabled"
fi
echo "Log File:        $LOG_FILE"
echo -e "${GREEN}================================${NC}"

# Build TLC command with advanced JVM options
TLC_CMD="java -XX:+UseParallelGC"
TLC_CMD="$TLC_CMD -Dtlc2.tool.fp.FPSet.impl=tlc2.tool.fp.OffHeapDiskFPSet"
TLC_CMD="$TLC_CMD -XX:MaxDirectMemorySize=${OFFHEAP_MEMORY}"
TLC_CMD="$TLC_CMD -Xmx${MEMORY} -Xms${MEMORY}"

# Add classpath
CP="$JAR_PATH"
if [ -f "$COMMUNITY_MODULES" ]; then
    CP="$COMMUNITY_MODULES:$CP"
fi
TLC_CMD="$TLC_CMD -cp $CP tlc2.TLC"

# Add config file
TLC_CMD="$TLC_CMD -config $CONFIG_FILE"

# Add spec file
TLC_CMD="$TLC_CMD $SPEC_FILE"

# Add workers
if [ "$WORKERS" != "auto" ]; then
    TLC_CMD="$TLC_CMD -workers $WORKERS"
else
    TLC_CMD="$TLC_CMD -workers auto"
fi

# Add deadlock check
if [ "$DEADLOCK_CHECK" = true ]; then
    TLC_CMD="$TLC_CMD -deadlock"
fi

# Add continue on error
if [ "$CONTINUE_ON_ERROR" = true ]; then
    TLC_CMD="$TLC_CMD -continue"
fi

# Mode-specific options
if [ "$SIMULATE_MODE" = true ]; then
    # Simulation mode
    if [ -n "$SIMULATE_FILE" ]; then
        SIM_OPTS="num=$SIMULATE_NUM,file=$SIMULATE_FILE"
    else
        SIM_OPTS="num=$SIMULATE_NUM"
    fi
    TLC_CMD="$TLC_CMD -simulate $SIM_OPTS"

    # Simulation depth (optional)
    if [ $SIMULATE_DEPTH -gt 0 ]; then
        TLC_CMD="$TLC_CMD -depth $SIMULATE_DEPTH"
    fi
else
    # Model checking mode
    if [ $CHECKPOINT_MINUTES -gt 0 ]; then
        TLC_CMD="$TLC_CMD -checkpoint $CHECKPOINT_MINUTES"
    fi

    if [ $MAX_DEPTH -gt 0 ]; then
        TLC_CMD="$TLC_CMD -depth $MAX_DEPTH"
    fi
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
    echo -e "${GREEN}✓ Completed successfully${NC}"
    if [ "$SIMULATE_MODE" = true ]; then
        echo -e "${GREEN}Traces generated at: $SIMULATE_FILE*${NC}"
    else
        echo -e "${GREEN}No errors found${NC}"
    fi
elif [ $EXIT_CODE -eq 124 ]; then
    echo -e "${YELLOW}⚠ Timed out${NC}"
elif [ $EXIT_CODE -eq 12 ]; then
    echo -e "${YELLOW}⚠ Invariant violation found!${NC}"
    echo -e "${YELLOW}Please check log: $LOG_FILE${NC}"
else
    echo -e "${YELLOW}⚠ Exited abnormally (exit code: $EXIT_CODE)${NC}"
fi
echo -e "${GREEN}================================${NC}"

exit $EXIT_CODE
