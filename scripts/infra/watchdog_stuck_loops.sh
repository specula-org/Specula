#!/usr/bin/env bash
#
# Watchdog: kill stuck `until grep ... ; sleep` wait-loops left by claude
# agents after TLC dies silently.
#
# Detection: a case's .specula-output/ has no file write in N minutes,
#            AND there are sleeping bash subshells under claude that match
#            the wait-loop cmdline pattern.
# Action:    SIGTERM the matching bash subshells (NOT claude itself).
#            claude receives SIGCHLD, tool call returns failure, agent
#            decides next step (typically moves to next phase).
#
# Usage:
#   nohup bash scripts/infra/watchdog_stuck_loops.sh \
#     --threshold 60 --interval 600 --case-pattern "_2" \
#     > logs/watchdog.log 2>&1 &

set -uo pipefail

THRESHOLD_MIN=60        # idle minutes before considered stuck
INTERVAL_SEC=600        # check every N seconds
CASE_PATTERN="_2"       # only watch case-studies matching this glob suffix
# Repo root, derived from this script's location (scripts/infra/). Override with
# $SPECULA_ROOT if the script is run from a copy outside the tree.
SPECULA_ROOT="${SPECULA_ROOT:-$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)}"

while [[ $# -gt 0 ]]; do
    case "$1" in
        --threshold) THRESHOLD_MIN="$2"; shift 2 ;;
        --interval)  INTERVAL_SEC="$2";  shift 2 ;;
        --case-pattern) CASE_PATTERN="$2"; shift 2 ;;
        *) echo "Unknown: $1" >&2; exit 1 ;;
    esac
done

log() { echo "[$(date '+%Y-%m-%d %H:%M:%S')] $*"; }

# Find bash subshells matching wait-loop pattern under given PID, recursively
find_stuck_bashes() {
    local parent_pid="$1"
    # Get claude PID (child of wrapper bash)
    local claude_pid
    claude_pid=$(pgrep -P "$parent_pid" 2>/dev/null | head -1)
    [[ -z "$claude_pid" ]] && return

    # Get bash subshells under claude
    local bpid cmdline
    for bpid in $(pgrep -P "$claude_pid" 2>/dev/null); do
        # Only bash processes
        [[ "$(cat /proc/$bpid/comm 2>/dev/null)" == "bash" ]] || continue
        cmdline=$(tr '\0' ' ' < "/proc/$bpid/cmdline" 2>/dev/null)
        # Wait-loop signature: 'until' or 'while' with 'sleep' in body
        if echo "$cmdline" | grep -qE "until[[:space:]].+do.*sleep|while[[:space:]].+do.*sleep|sleep[[:space:]]+[0-9]+;[[:space:]]*done"; then
            echo "$bpid"
        fi
    done
}

check_case() {
    local case_dir="$1"
    local case_name
    case_name=$(basename "$case_dir")
    local outdir="$case_dir/.specula-output"

    [[ -d "$outdir" ]] || return
    [[ -f "$outdir/pipeline-summary.md" ]] && return    # done

    # Find latest mtime of any file under outdir
    local latest_mtime
    latest_mtime=$(find "$outdir" -type f -printf '%T@\n' 2>/dev/null | sort -n | tail -1)
    [[ -z "$latest_mtime" ]] && return

    local now idle_sec
    now=$(date +%s)
    idle_sec=$(awk -v n=$now -v l=$latest_mtime 'BEGIN{printf "%d", int(n-l)}')

    (( idle_sec < THRESHOLD_MIN * 60 )) && return    # still active

    # Find currently-active phase's wrapper PID
    local wrapper_pid="" pid_path
    for phase in bug-confirmation spec-validation harness-gen spec-gen agent; do
        pid_path="$outdir/${phase}.pid"
        if [[ -f "$pid_path" ]]; then
            local pid
            pid=$(cat "$pid_path" 2>/dev/null)
            if [[ -n "$pid" ]] && ps -p "$pid" > /dev/null 2>&1; then
                wrapper_pid="$pid"
                break
            fi
        fi
    done
    [[ -z "$wrapper_pid" ]] && return

    # Find stuck bash subshells
    local stuck_bashes
    stuck_bashes=$(find_stuck_bashes "$wrapper_pid")
    if [[ -z "$stuck_bashes" ]]; then
        log "$case_name: idle ${idle_sec}s but no stuck wait-loop pattern detected (might be busy via other tools)"
        return
    fi

    local count
    count=$(echo "$stuck_bashes" | wc -w)
    log "$case_name: STUCK detected (idle ${idle_sec}s, $count wait-loop bash). Killing: $stuck_bashes"
    for bpid in $stuck_bashes; do
        kill -TERM "$bpid" 2>/dev/null && log "  killed bash $bpid"
    done
}

log "Watchdog started: threshold=${THRESHOLD_MIN}min, interval=${INTERVAL_SEC}s, pattern=*${CASE_PATTERN}"

while true; do
    for case_dir in "$SPECULA_ROOT"/case-studies/*${CASE_PATTERN}/; do
        [[ -d "$case_dir" ]] || continue
        check_case "$case_dir"
    done
    sleep "$INTERVAL_SEC"
done
