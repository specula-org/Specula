#!/bin/bash
################################################################################
# Generic Model Check Script
# Usage: ./run_model_check.sh -s SPEC_FILE -c CONFIG_FILE [options]
# ex: nohup ../../../../../../scripts/tlc/run_model_check.sh -s MCetcdraft.tla -c MCetcdraft.cfg -m 50G -w 90 -t 120 -D -S -p 200 -n 99999999 -A -o nohup.out & 
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
CDOT_MODE=false
JSON_DUMPTRACE=""

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
    echo "  -j FILE    Enable JSON trace dump format"
    echo "  -h         Show this help"
    echo ""
    echo "Run Resource Budget:"
    echo "  SPECULA_TLC_MEMORY_LIMIT=SIZE  Aggregate heap + off-heap bound"
    echo "                                  (default: auto, 80% available at first TLC start)"
    echo "  SPECULA_TLC_WORKER_LIMIT=NUM   Optional aggregate worker bound"
    echo ""
    echo "Model Checking Options:"
    echo "  -d NUM     Max depth (default: 0, no limit)"
    echo "  -k MIN     Checkpoint interval (default: 10)"
    echo "  -D         Enable deadlock checking"
    echo "  -C         Continue after finding errors (find all violations)"
    echo "  -A         Enable action composition (cdot) support"
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
while getopts "s:c:m:M:j:w:t:d:k:o:SDCAn:f:p:h" opt; do
    case $opt in
        s) SPEC_FILE="$OPTARG" ;;
        c) CONFIG_FILE="$OPTARG" ;;
        m) MEMORY="$OPTARG" ;;
        M) OFFHEAP_MEMORY="$OPTARG" ;;
        j) JSON_DUMPTRACE="$OPTARG" ;;
        w) WORKERS="$OPTARG" ;;
        t) TIMEOUT_MINUTES="$OPTARG" ;;
        d) MAX_DEPTH="$OPTARG" ;;
        k) CHECKPOINT_MINUTES="$OPTARG" ;;
        o) LOG_FILE="$OPTARG" ;;
        S) SIMULATE_MODE=true ;;
        D) DEADLOCK_CHECK=true ;;
        C) CONTINUE_ON_ERROR=true ;;
        A) CDOT_MODE=true ;;
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

# Resolve one runtime root for every bundled TLC dependency. A relocated
# wrapper may be reached through a symlink, while SPECULA_ROOT points at the
# installed Specula tree that owns the jars, guard, and worker probe.
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
RUNTIME_ROOT="$PROJECT_ROOT"
if [ ! -f "$RUNTIME_ROOT/lib/tla2tools.jar" ] \
    && [ -n "${SPECULA_ROOT:-}" ] \
    && [ -f "$SPECULA_ROOT/lib/tla2tools.jar" ]; then
    RUNTIME_ROOT="$(cd "$SPECULA_ROOT" && pwd)" || {
        echo "Error: cannot resolve SPECULA_ROOT: $SPECULA_ROOT"
        exit 1
    }
fi
JAR_PATH="$RUNTIME_ROOT/lib/tla2tools.jar"
COMMUNITY_MODULES="$RUNTIME_ROOT/lib/CommunityModules-deps.jar"

if [ ! -f "$JAR_PATH" ]; then
    echo "Error: tla2tools.jar not found at $JAR_PATH"
    exit 1
fi

RESOURCE_GUARD="$RUNTIME_ROOT/src/specula/tlc_resources.py"
if [ ! -f "$RESOURCE_GUARD" ]; then
    echo "Error: TLC resource guard not found at $RESOURCE_GUARD"
    exit 1
fi

# TLC resolves -workers auto once, at JVM startup. Resolve it with the same JVM
# API for accounting, but continue passing "auto" to TLC itself.
if [ "$WORKERS" = "auto" ]; then
    RESOLVED_WORKERS="$(java "$RUNTIME_ROOT/scripts/tlc/PrintAvailableProcessors.java" 2>/dev/null)"
else
    RESOLVED_WORKERS="$WORKERS"
fi
if ! [[ "$RESOLVED_WORKERS" =~ ^[1-9][0-9]*$ ]]; then
    echo "Error: workers (-w) must be 'auto' or a positive integer (resolved: '$RESOLVED_WORKERS')."
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
TLC_CMD=(
    java
    -XX:+UseParallelGC
    -Dtlc2.tool.fp.FPSet.impl=tlc2.tool.fp.OffHeapDiskFPSet
    "-XX:MaxDirectMemorySize=${OFFHEAP_MEMORY}"
    "-Xmx${MEMORY}"
    "-Xms${MEMORY}"
)

# Add cdot support if enabled
if [ "$CDOT_MODE" = true ]; then
    TLC_CMD+=(-Dtlc2.tool.impl.Tool.cdot=true)
fi

# Add classpath
CP="$JAR_PATH"
if [ -f "$COMMUNITY_MODULES" ]; then
    CP="$COMMUNITY_MODULES:$CP"
fi
TLC_CMD+=(-cp "$CP" tlc2.TLC)

# Add config file
TLC_CMD+=(-config "$CONFIG_FILE")

# Add spec file
TLC_CMD+=("$SPEC_FILE")

# Add workers
TLC_CMD+=(-workers "$WORKERS")

# Add deadlock check
if [ "$DEADLOCK_CHECK" = true ]; then
    TLC_CMD+=(-deadlock)
fi

# Add continue on error
if [ "$CONTINUE_ON_ERROR" = true ]; then
    TLC_CMD+=(-continue)
fi

# Mode-specific options
if [ "$SIMULATE_MODE" = true ]; then
    # Simulation mode
    if [ -n "$SIMULATE_FILE" ]; then
        SIM_OPTS="num=$SIMULATE_NUM,file=$SIMULATE_FILE"
    else
        SIM_OPTS="num=$SIMULATE_NUM"
    fi
    TLC_CMD+=(-simulate "$SIM_OPTS")

    # Simulation depth (optional)
    if [ $SIMULATE_DEPTH -gt 0 ]; then
        TLC_CMD+=(-depth "$SIMULATE_DEPTH")
    fi
else
    # Model checking mode
    if [ $CHECKPOINT_MINUTES -gt 0 ]; then
        TLC_CMD+=(-checkpoint "$CHECKPOINT_MINUTES")
    fi

    if [ $MAX_DEPTH -gt 0 ]; then
        TLC_CMD+=(-depth "$MAX_DEPTH")
    fi
fi

# Resolve the timeout here, but keep Java as the direct lease owner. A separate
# watchdog below enforces the deadline; wrapping Java in GNU timeout would make
# timeout's PID the owner and could undercount a surviving Java child if timeout
# itself were SIGKILLed.
TIMEOUT_SECONDS=0
if [ $TIMEOUT_MINUTES -gt 0 ]; then
    TIMEOUT_SECONDS=$((TIMEOUT_MINUTES * 60))
fi

# Add JSON dumptrace
if [ "$JSON_DUMPTRACE" != "" ]; then
    TLC_CMD+=(-dumptrace json "$JSON_DUMPTRACE")
fi


# TLC spills its state graph (often many GB) into the -metadir. Default to the
# system temp dir, honoring $TMPDIR; set $TLC_STATE_DIR to redirect onto a larger
# or faster volume. We deliberately do NOT default to /dev/shm: it is RAM-backed
# and large hunts would exhaust memory on machines with modest RAM.
_TLC_TMP_BASE="${TLC_STATE_DIR:-${TMPDIR:-/tmp}}"
METADIR="$(mktemp -d "${_TLC_TMP_BASE%/}/tlc-states-XXXXXX")"
TLC_CMD+=(-metadir "$METADIR")

CONTROL_DIR="$(mktemp -d "${TMPDIR:-/tmp}/specula-tlc-control-XXXXXX")"
LEASE_FILE="$CONTROL_DIR/lease.json"
START_FILE="$CONTROL_DIR/start"
STOP_FILE="$CONTROL_DIR/stop"
OWNER_STATUS="$CONTROL_DIR/owner-status"
ADMISSION_OUTPUT_FILE="$CONTROL_DIR/admission-output"
TLC_PID=""
WATCHDOG_PID=""
WATCHDOG_STATUS="$CONTROL_DIR/watchdog-status"

cleanup() {
    local rc=$?
    trap - EXIT
    if [ -n "$WATCHDOG_PID" ] && kill -0 "$WATCHDOG_PID" 2>/dev/null; then
        kill "$WATCHDOG_PID" 2>/dev/null || true
        wait "$WATCHDOG_PID" 2>/dev/null || true
    fi
    if [ -n "$TLC_PID" ] && kill -0 "$TLC_PID" 2>/dev/null; then
        kill "$TLC_PID" 2>/dev/null || true
        wait "$TLC_PID" 2>/dev/null || true
    fi
    if [ -s "$LEASE_FILE" ]; then
        python3 "$RESOURCE_GUARD" release --lease-file "$LEASE_FILE" >/dev/null 2>&1 \
            || echo "Warning: could not release TLC resource reservation." >&2
    fi
    rm -rf "$CONTROL_DIR" "$METADIR"
    exit "$rc"
}
trap cleanup EXIT

publish_admission() {
    local status="$1"
    local owner_pid="$2"
    local output="$3"
    local status_file="${SPECULA_TLC_ADMISSION_STATUS:-}"
    [ -n "$status_file" ] || return 0
    local tmp="${status_file}.$$.tmp"
    {
        printf '%s\n' "$status"
        printf '%s\n' "$owner_pid"
        printf '%s\n' "$output"
    } > "$tmp" && mv -f "$tmp" "$status_file"
}

process_running() {
    local pid="$1"
    local state
    [ -n "$pid" ] || return 1
    state="$(ps -o stat= -p "$pid" 2>/dev/null || true)"
    kill -0 "$pid" 2>/dev/null && [[ "$state" != Z* ]]
}

register_owner_with_stop_gate() {
    local gate_work_dir="${SPECULA_STOP_GATE_WORK_DIR:-${SPECULA_WORK_DIR:-}}"
    [ -n "$gate_work_dir" ] || return 0
    local registry_dir="$gate_work_dir/.stop-gate/background-pids"
    local registry_file="$registry_dir/${TLC_PID}.pid"
    local registry_tmp="$registry_dir/.${TLC_PID}.$$.owner.tmp"
    if mkdir -p "$registry_dir" \
        && printf '%s\n' "$TLC_PID" > "$registry_tmp" \
        && mv -f "$registry_tmp" "$registry_file"; then
        return 0
    fi
    rm -f "$registry_tmp" 2>/dev/null || true
    return 1
}

echo -e "${YELLOW}Executing Command:${NC}"
printf '%q ' "${TLC_CMD[@]}"
echo ""
echo ""

# The resource owner takes a lifetime flock in the shared run state, publishes
# admission, waits for START, and then execs Java without changing PID. The lock
# therefore remains held by Java even if this wrapper is SIGKILLed, and remains
# visible to admissions in other PID namespaces.
python3 "$RESOURCE_GUARD" owner \
    --heap "$MEMORY" \
    --offheap "$OFFHEAP_MEMORY" \
    --workers "$RESOLVED_WORKERS" \
    --workers-label "$WORKERS" \
    --lease-file "$LEASE_FILE" \
    --status-file "$OWNER_STATUS" \
    --report-file "$ADMISSION_OUTPUT_FILE" \
    --start-file "$START_FILE" \
    --stop-file "$STOP_FILE" \
    --parent-pid "$$" \
    -- "${TLC_CMD[@]}" > >(tee "$LOG_FILE") 2>&1 &
TLC_PID=$!

for _ in {1..600}; do
    if [ -s "$OWNER_STATUS" ]; then
        break
    fi
    if ! process_running "$TLC_PID"; then
        wait "$TLC_PID" 2>/dev/null
        ADMISSION_RC=$?
        TLC_PID=""
        [ "$ADMISSION_RC" -ne 0 ] || ADMISSION_RC=2
        ADMISSION_OUTPUT="$(cat "$ADMISSION_OUTPUT_FILE" 2>/dev/null || true)"
        [ -n "$ADMISSION_OUTPUT" ] || ADMISSION_OUTPUT="TLC resource owner exited before publishing admission."
        printf '%s\n' "$ADMISSION_OUTPUT" >&2
        publish_admission rejected "" "$ADMISSION_OUTPUT" || true
        exit "$ADMISSION_RC"
    fi
    sleep 0.05
done

if [ ! -s "$OWNER_STATUS" ]; then
    ADMISSION_OUTPUT="TLC resource owner did not publish admission within 30 seconds."
    echo "Error: $ADMISSION_OUTPUT" >&2
    touch "$STOP_FILE"
    kill "$TLC_PID" 2>/dev/null || true
    wait "$TLC_PID" 2>/dev/null || true
    TLC_PID=""
    publish_admission rejected "" "$ADMISSION_OUTPUT" || true
    exit 2
fi

ADMISSION_RESULT="$(tr -d '[:space:]' < "$OWNER_STATUS")"
ADMISSION_OUTPUT="$(cat "$ADMISSION_OUTPUT_FILE" 2>/dev/null || true)"
printf '%s\n' "$ADMISSION_OUTPUT"

if [ "$ADMISSION_RESULT" != "admitted" ]; then
    touch "$STOP_FILE"
    publish_admission rejected "" "$ADMISSION_OUTPUT" || true
    wait "$TLC_PID" 2>/dev/null
    ADMISSION_RC=$?
    TLC_PID=""
    [ "$ADMISSION_RC" -ne 0 ] || ADMISSION_RC=2
    exit "$ADMISSION_RC"
fi

if [ "$TIMEOUT_SECONDS" -gt 0 ]; then
    python3 "$RESOURCE_GUARD" watchdog \
        --pid "$TLC_PID" \
        --seconds "$TIMEOUT_SECONDS" \
        --status-file "$WATCHDOG_STATUS" &
    WATCHDOG_PID=$!
    WATCHDOG_READY=false
    for _ in {1..100}; do
        if grep -qx 'ready' "$WATCHDOG_STATUS" 2>/dev/null; then
            WATCHDOG_READY=true
            break
        fi
        if ! process_running "$WATCHDOG_PID"; then
            wait "$WATCHDOG_PID" 2>/dev/null
            WATCHDOG_RC=$?
            WATCHDOG_PID=""
            WATCHDOG_ERROR="TLC timeout watchdog failed during startup (exit $WATCHDOG_RC)."
            echo "Error: $WATCHDOG_ERROR" >&2
            touch "$STOP_FILE"
            publish_admission rejected "" "$WATCHDOG_ERROR" || true
            wait "$TLC_PID" 2>/dev/null || true
            TLC_PID=""
            exit 2
        fi
        sleep 0.05
    done
    if [ "$WATCHDOG_READY" != true ]; then
        WATCHDOG_ERROR="TLC timeout watchdog did not become ready."
        echo "Error: $WATCHDOG_ERROR" >&2
        touch "$STOP_FILE"
        publish_admission rejected "" "$WATCHDOG_ERROR" || true
        exit 2
    fi
fi

# The long-lived wrapper owns this registration instead of relying on the
# short-lived background launcher. Publish the stable holder/Java PID before
# START so even SIGKILL during launcher handoff cannot hide a live TLC from the
# agent stop gate.
if ! register_owner_with_stop_gate; then
    WATCHDOG_ERROR="could not register the TLC owner with the Specula stop gate."
    echo "Error: $WATCHDOG_ERROR" >&2
    touch "$STOP_FILE"
    publish_admission rejected "" "$WATCHDOG_ERROR" || true
    exit 2
fi

touch "$START_FILE"
if ! publish_admission admitted "$TLC_PID" "$ADMISSION_OUTPUT"; then
    echo "Error: could not report TLC admission to the background launcher." >&2
    exit 2
fi

WATCHDOG_FAILED=false
WATCHDOG_TIMED_OUT=false
if [ -n "$WATCHDOG_PID" ]; then
    while process_running "$TLC_PID"; do
        if ! process_running "$WATCHDOG_PID"; then
            wait "$WATCHDOG_PID" 2>/dev/null
            WATCHDOG_RC=$?
            WATCHDOG_PID=""
            if [ "$WATCHDOG_RC" -eq 124 ]; then
                WATCHDOG_TIMED_OUT=true
            else
                WATCHDOG_FAILED=true
                echo "Error: TLC timeout watchdog exited while TLC was running (exit $WATCHDOG_RC); stopping TLC." >&2
                kill "$TLC_PID" 2>/dev/null || true
            fi
            break
        fi
        sleep 0.1
    done
fi

wait "$TLC_PID"
EXIT_CODE=$?
TLC_PID=""
WATCHDOG_STOPPED=false
if [ -n "$WATCHDOG_PID" ] && process_running "$WATCHDOG_PID"; then
    kill "$WATCHDOG_PID" 2>/dev/null || true
    WATCHDOG_STOPPED=true
fi
if [ -n "$WATCHDOG_PID" ]; then
    wait "$WATCHDOG_PID" 2>/dev/null
    WATCHDOG_RC=$?
    WATCHDOG_PID=""
    if [ "$WATCHDOG_STOPPED" != true ]; then
        if [ "$WATCHDOG_RC" -eq 124 ]; then
            WATCHDOG_TIMED_OUT=true
        elif [ "$WATCHDOG_RC" -ne 0 ]; then
            WATCHDOG_FAILED=true
            echo "Error: TLC timeout watchdog failed (exit $WATCHDOG_RC)." >&2
        fi
    fi
fi
if [ "$WATCHDOG_FAILED" = true ]; then
    EXIT_CODE=2
elif [ "$WATCHDOG_TIMED_OUT" = true ]; then
    EXIT_CODE=124
fi
# Drain the process-substitution tee before printing the final status.
wait 2>/dev/null || true

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
