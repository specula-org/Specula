#!/usr/bin/env bash
################################################################################
# wait_for_tlc.sh — wait for a background TLC (or any long-running job) to exit.
#
# Replaces the fragile pattern:
#
#   until grep -qE "Finished in|Error" out.log; do sleep 60; done
#
# That pattern spins forever if the subprocess was killed by SIGTERM (e.g.
# TLC's own `-t` budget hitting), because TLC never writes "Finished in"
# when it is signaled.
#
# This helper instead blocks on the PID itself via `tail --pid`, so any kind
# of exit (natural, SIGTERM, SIGKILL, OOM) unblocks it. An outer timeout
# bounds the wait as a backstop.
#
# Usage:
#   wait_for_tlc.sh --pid-file PATH [--timeout DUR] [--log PATH] [--quiet]
#   wait_for_tlc.sh --pid PID       [--timeout DUR] [--log PATH] [--quiet]
#
# Args:
#   --pid-file PATH   File containing the PID written by start_background.sh
#   --pid PID         PID to wait on (alternative to --pid-file)
#   --timeout DUR     Outer wait cap. `timeout(1)` syntax: 90s, 30m, 1h, 4h.
#                     Default: 1h. Pass "none" to wait indefinitely.
#   --log PATH        Optional log file; printed-summary lines come from here.
#   --quiet           Suppress the post-mortem summary scan.
#
# Exit codes:
#   0   process exited (naturally OR via signal) within the timeout
#   124 outer timeout fired before the process exited (process still alive)
#   2   bad usage / missing PID file
#   3   PID file present but process not running at start (already gone)
################################################################################

set -uo pipefail

PID=""
PID_FILE=""
TIMEOUT_DUR="1h"
LOG_FILE=""
QUIET=0

usage() {
    sed -n '3,33p' "$0"
    exit 2
}

while [[ $# -gt 0 ]]; do
    case "$1" in
        --pid)      PID="$2"; shift 2 ;;
        --pid-file) PID_FILE="$2"; shift 2 ;;
        --timeout)  TIMEOUT_DUR="$2"; shift 2 ;;
        --log)      LOG_FILE="$2"; shift 2 ;;
        --quiet)    QUIET=1; shift ;;
        -h|--help)  usage ;;
        *) echo "wait_for_tlc.sh: unknown arg: $1" >&2; usage ;;
    esac
done

if [[ -z "$PID" && -z "$PID_FILE" ]]; then
    echo "wait_for_tlc.sh: must pass --pid or --pid-file" >&2
    exit 2
fi

if [[ -n "$PID_FILE" ]]; then
    if [[ ! -f "$PID_FILE" ]]; then
        echo "wait_for_tlc.sh: pid-file not found: $PID_FILE" >&2
        exit 2
    fi
    PID=$(cat "$PID_FILE" | tr -d '[:space:]')
fi

if ! [[ "$PID" =~ ^[0-9]+$ ]]; then
    echo "wait_for_tlc.sh: invalid pid: '$PID'" >&2
    exit 2
fi

summarize_log() {
    local log="$1"
    echo ""
    echo "--- log summary ($log) ---"
    # Recognize TLC termination markers and common failure modes. Add lines
    # here as new markers show up; this is the post-mortem hint, not the
    # wait condition.
    if grep -qE "Finished in" "$log" 2>/dev/null; then
        grep -E "Finished in|states generated|distinct states|fingerprint" "$log" | tail -8
    elif grep -qE "Invariant .* is violated" "$log" 2>/dev/null; then
        echo "RESULT: invariant violated"
        grep -E "Invariant .* is violated|Error: " "$log" | head -4
    elif grep -qiE "out of memory|OutOfMemoryError|java.lang.OutOfMemory" "$log" 2>/dev/null; then
        echo "RESULT: out-of-memory"
        grep -iE "out of memory|OutOfMemoryError" "$log" | head -2
    elif grep -qiE "killed|terminated|signal" "$log" 2>/dev/null; then
        echo "RESULT: signaled (likely TLC's own -t budget, or external kill)"
        tail -4 "$log"
    elif grep -qE "Error|Exception" "$log" 2>/dev/null; then
        echo "RESULT: errored"
        grep -E "Error|Exception" "$log" | head -4
    else
        echo "RESULT: exited without recognized marker (tail follows)"
        tail -6 "$log"
    fi
    echo "--- end summary ---"
}

if ! kill -0 "$PID" 2>/dev/null; then
    echo "wait_for_tlc.sh: pid $PID not running at start (already exited)"
    [[ $QUIET -eq 0 && -n "$LOG_FILE" && -f "$LOG_FILE" ]] && summarize_log "$LOG_FILE"
    exit 3
fi

START_TS=$(date +%s)
echo "wait_for_tlc.sh: waiting on pid $PID (timeout=$TIMEOUT_DUR)"

if [[ "$TIMEOUT_DUR" == "none" ]]; then
    tail --pid="$PID" -f /dev/null
    RC=0
else
    timeout "$TIMEOUT_DUR" tail --pid="$PID" -f /dev/null
    RC=$?
fi

ELAPSED=$(( $(date +%s) - START_TS ))

if [[ $RC -eq 124 ]]; then
    echo "wait_for_tlc.sh: OUTER TIMEOUT after ${ELAPSED}s (timeout=$TIMEOUT_DUR); pid $PID still alive"
    [[ $QUIET -eq 0 && -n "$LOG_FILE" && -f "$LOG_FILE" ]] && summarize_log "$LOG_FILE"
    exit 124
fi

# tail exited because the process died. Distinguish natural vs signal by
# checking the kernel's exit info; without parent rights we can't reap it,
# so just observe that it's gone.
if kill -0 "$PID" 2>/dev/null; then
    # Shouldn't happen — tail --pid returned but pid still alive.
    echo "wait_for_tlc.sh: tail returned $RC but pid $PID still alive; treating as error"
    exit 1
fi

echo "wait_for_tlc.sh: pid $PID exited after ${ELAPSED}s"
[[ $QUIET -eq 0 && -n "$LOG_FILE" && -f "$LOG_FILE" ]] && summarize_log "$LOG_FILE"
exit 0
