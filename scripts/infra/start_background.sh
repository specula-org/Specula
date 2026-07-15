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

WORK_DIR="$(cd "$WORK_DIR" && pwd)"
if [[ "$LOG_FILE" = /* ]]; then
    LOG_PATH="$LOG_FILE"
else
    LOG_PATH="$WORK_DIR/$LOG_FILE"
fi

LOG_DIR="$(dirname "$LOG_PATH")"
if [ ! -d "$LOG_DIR" ]; then
    echo "Error: Log directory $LOG_DIR does not exist."
    exit 1
fi

echo "Starting model check in background..."
echo "Working Directory: $WORK_DIR"
echo "Log File:          $LOG_PATH"
echo "Arguments:         ${PASSTHROUGH_ARGS[*]}"

# Start the wrapper and wait only for its resource-admission handshake. This
# keeps the long TLC run in the background while returning an over-budget error
# (and the useful budget numbers) directly to the agent instead of burying it in
# the log after reporting a false-successful launch.
# We cd to WORK_DIR so relative paths for spec/config work.
cd "$WORK_DIR"
ADMISSION_DIR="$(mktemp -d "${TMPDIR:-/tmp}/specula-tlc-admission-XXXXXX")"
ADMISSION_FILE="$ADMISSION_DIR/status"
SPECULA_TLC_ADMISSION_STATUS="$ADMISSION_FILE" \
    nohup "$RUN_SCRIPT" "${PASSTHROUGH_ARGS[@]}" > "$LOG_PATH" 2>&1 &
PID=$!
PID_FILE=""
REGISTRY_FILE=""
OWNER_REGISTRY_FILE=""
MANAGED=false

cancel_unmanaged_launch() {
    local rc="$1"
    trap - INT TERM HUP
    if [ "$MANAGED" != true ]; then
        kill "$PID" 2>/dev/null || true
        wait "$PID" 2>/dev/null || true
        [ -z "$PID_FILE" ] || rm -f "$PID_FILE"
        [ -z "$REGISTRY_FILE" ] || rm -f "$REGISTRY_FILE"
        [ -z "$OWNER_REGISTRY_FILE" ] || rm -f "$OWNER_REGISTRY_FILE"
    fi
    rm -rf "$ADMISSION_DIR"
    exit "$rc"
}
trap 'cancel_unmanaged_launch 130' INT
trap 'cancel_unmanaged_launch 143' TERM
trap 'cancel_unmanaged_launch 129' HUP

for _ in {1..300}; do
    if [ -s "$ADMISSION_FILE" ]; then
        break
    fi
    if ! kill -0 "$PID" 2>/dev/null; then
        wait "$PID" 2>/dev/null
        RC=$?
        [ "$RC" -ne 0 ] || RC=2
        echo "ERROR: model-check wrapper exited before resource admission (exit $RC)." >&2
        tail -n 20 "$LOG_PATH" >&2 2>/dev/null || true
        rm -rf "$ADMISSION_DIR"
        exit "$RC"
    fi
    sleep 0.1
done

if [ ! -s "$ADMISSION_FILE" ]; then
    echo "ERROR: timed out waiting for TLC resource admission; stopping process $PID." >&2
    kill "$PID" 2>/dev/null || true
    wait "$PID" 2>/dev/null || true
    rm -rf "$ADMISSION_DIR"
    exit 2
fi

ADMISSION_RESULT="$(sed -n '1p' "$ADMISSION_FILE")"
ADMISSION_OWNER="$(sed -n '2p' "$ADMISSION_FILE")"
tail -n +3 "$ADMISSION_FILE"
rm -rf "$ADMISSION_DIR"

if [ "$ADMISSION_RESULT" != "admitted" ]; then
    wait "$PID" 2>/dev/null
    RC=$?
    [ "$RC" -ne 0 ] || RC=2
    echo "ERROR: model check was not started." >&2
    exit "$RC"
fi
if ! [[ "$ADMISSION_OWNER" =~ ^[1-9][0-9]*$ ]]; then
    echo "ERROR: model-check wrapper returned an invalid TLC owner PID: '$ADMISSION_OWNER'." >&2
    kill "$PID" 2>/dev/null || true
    wait "$PID" 2>/dev/null || true
    exit 2
fi

# Give an immediately completing TLC a brief chance to be reaped, then avoid
# handing back a stale PID as a live background job.
sleep 0.05
PROCESS_STATE="$(ps -o stat= -p "$PID" 2>/dev/null || true)"
if ! kill -0 "$PID" 2>/dev/null || [[ "$PROCESS_STATE" = Z* ]]; then
    wait "$PID" 2>/dev/null
    RC=$?
    if [ "$RC" -eq 0 ]; then
        echo "✓ Model check completed successfully before background PID handoff."
        echo "  Log File: $LOG_PATH"
        exit 0
    fi
    echo "ERROR: model-check wrapper exited immediately after admission (exit $RC)." >&2
    tail -n 20 "$LOG_PATH" >&2 2>/dev/null || true
    exit "$RC"
fi

PID_FILE="$LOG_PATH.pid"
echo "$PID" > "$PID_FILE"

# A parallel confirmation worker deliberately narrows its stop-gate scan to the
# finding directory. Register managed jobs there as well as next to their logs,
# so an absolute/out-of-scope log path or a pruned TLC directory cannot hide a
# live process from the gate. Outside a Specula agent run the env var is absent
# and this helper keeps its historical standalone behaviour.
GATE_WORK_DIR="${SPECULA_STOP_GATE_WORK_DIR:-${SPECULA_WORK_DIR:-}}"
if [[ -n "$GATE_WORK_DIR" ]]; then
    REGISTRY_DIR="$GATE_WORK_DIR/.stop-gate/background-pids"
    REGISTRY_TMP="$REGISTRY_DIR/.${PID}.$$.tmp"
    OWNER_REGISTRY_TMP="$REGISTRY_DIR/.${ADMISSION_OWNER}.$$.tmp"
    REGISTRY_FILE="$REGISTRY_DIR/${PID}.pid"
    OWNER_REGISTRY_FILE="$REGISTRY_DIR/${ADMISSION_OWNER}.pid"
    if mkdir -p "$REGISTRY_DIR" \
        && printf '%s\n%s\n' "$PID" "$PID_FILE" > "$REGISTRY_TMP" \
        && mv -f "$REGISTRY_TMP" "$REGISTRY_FILE" \
        && printf '%s\n%s\n' "$ADMISSION_OWNER" "$PID_FILE" > "$OWNER_REGISTRY_TMP" \
        && mv -f "$OWNER_REGISTRY_TMP" "$OWNER_REGISTRY_FILE"; then
        echo "  Gate registry: $REGISTRY_FILE"
        echo "  TLC registry:  $OWNER_REGISTRY_FILE"
    else
        rm -f "$REGISTRY_TMP" "$OWNER_REGISTRY_TMP" "$REGISTRY_FILE" "$OWNER_REGISTRY_FILE" 2>/dev/null || true
        echo "ERROR: could not register PID with the Specula stop gate; stopping untracked job $PID" >&2
        kill "$PID" 2>/dev/null || true
        wait "$PID" 2>/dev/null || true
        rm -f "$PID_FILE"
        exit 1
    fi
fi

MANAGED=true
trap - INT TERM HUP

echo ""
echo "✓ Process started! PID: $PID"
echo "  TLC owner:   $ADMISSION_OWNER"
echo "  PID file:    $PID_FILE"
echo "  Wait:        $SCRIPT_DIR/wait_for_pid.sh --pid-file $PID_FILE --timeout 1h --log $LOG_PATH"
echo "  Monitor:     tail -f $LOG_PATH"
echo "  Stop:        kill $PID"
