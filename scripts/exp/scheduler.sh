#!/usr/bin/env bash
#
# Overnight batch scheduler for Specula pipeline.
#
# Runs tasks from a queue file with N parallel workers.
# Pauses when usage exceeds threshold, waits for 5-hour window reset, resumes.
# Stops after exhausting MAX_WINDOWS resets.
#
# Usage:
#   bash scripts/exp/scheduler.sh [options]
#
# Options:
#   --workers N      Parallel workers (default: 3)
#   --threshold N    Usage % to pause at (default: 80)
#   --windows N      Max resets to wait through (default: 3)
#   --queue FILE     Task queue file (default: scripts/exp/tasks.queue)
#   --max-turns N    Max agent turns per task (default: 0 = unlimited)
#   --setup-only     Only clone repos and write prompts, don't run pipeline
#   --dry-run        Print commands without executing
#
# Queue format (tab-separated):
#   name|github|lang|reference[TAB]flags[TAB]prompt_file
#
#   - flags: optional launch_pipeline.sh flags (e.g. --skip-analysis)
#   - prompt_file: optional path to extra prompt (relative to queue dir)
#     Content is written to case-studies/<name>/.prompt-extra.md before launch.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SPECULA_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"

WORKERS=3
THRESHOLD=80
MAX_WINDOWS=3
QUEUE_FILE="$SCRIPT_DIR/tasks.queue"
MAX_TURNS=0
PROMPT_FILE=""
DRY_RUN=false
SETUP_ONLY=false

while [[ $# -gt 0 ]]; do
  case "$1" in
    --workers)    WORKERS="$2";    shift 2 ;;
    --threshold)  THRESHOLD="$2";  shift 2 ;;
    --windows)    MAX_WINDOWS="$2"; shift 2 ;;
    --queue)      QUEUE_FILE="$2"; shift 2 ;;
    --max-turns)  MAX_TURNS="$2";  shift 2 ;;
    --prompt)     PROMPT_FILE="$2"; shift 2 ;;
    --setup-only) SETUP_ONLY=true; shift ;;
    --dry-run)    DRY_RUN=true;    shift ;;
    -h|--help)    sed -n '2,/^$/s/^# \?//p' "$0"; exit 0 ;;
    *)            echo "Unknown: $1" >&2; exit 1 ;;
  esac
done

# Resolve prompt file to absolute path
if [[ -n "$PROMPT_FILE" && ! "$PROMPT_FILE" =~ ^/ ]]; then
  PROMPT_FILE="$(cd "$(dirname "$PROMPT_FILE")" && pwd)/$(basename "$PROMPT_FILE")"
fi

# --- Logging & dirs ---

RUN_ID="$(date +%Y%m%d_%H%M%S)"
LOG_DIR="$SPECULA_ROOT/logs/scheduler/$RUN_ID"
mkdir -p "$LOG_DIR/status"

log() { echo "[$(date '+%Y-%m-%d %H:%M:%S')] $*" | tee -a "$LOG_DIR/scheduler.log"; }

# --- Usage gate ---

WINDOWS_USED=0

check_usage() {
  local tmp="$LOG_DIR/.usage.json"
  bash "$SCRIPT_DIR/usage.sh" > "$tmp" 2>/dev/null || { log "WARN: usage fetch failed"; return 0; }

  python3 - "$tmp" "$THRESHOLD" "$LOG_DIR/.reset_at" <<'PYEOF'
import json, sys

with open(sys.argv[1]) as f:
    d = json.load(f)
threshold = float(sys.argv[2])
reset_file = sys.argv[3]

resets = []
for key in ('five_hour', 'seven_day'):
    obj = d.get(key)
    if obj and obj.get('utilization', 0) > threshold:
        resets.append(obj.get('resets_at', ''))

if resets:
    earliest = sorted([r for r in resets if r])[0] if any(resets) else ''
    with open(reset_file, 'w') as f:
        f.write(earliest)
    sys.exit(1)
sys.exit(0)
PYEOF
}

wait_for_quota() {
  while ! check_usage; do
    WINDOWS_USED=$((WINDOWS_USED + 1))
    if (( WINDOWS_USED > MAX_WINDOWS )); then
      log "Max resets ($MAX_WINDOWS) exhausted, stopping scheduler"
      return 1
    fi

    local reset_at sleep_secs
    reset_at="$(cat "$LOG_DIR/.reset_at" 2>/dev/null || echo "")"
    if [[ -n "$reset_at" ]]; then
      sleep_secs=$(( $(date -d "$reset_at" +%s) - $(date +%s) + 120 ))
      (( sleep_secs < 60 )) && sleep_secs=60
      log "Over ${THRESHOLD}%, sleeping ${sleep_secs}s until $reset_at (reset $WINDOWS_USED/$MAX_WINDOWS)"
    else
      sleep_secs=600
      log "Over ${THRESHOLD}%, no reset time, sleeping ${sleep_secs}s"
    fi
    sleep "$sleep_secs"
  done
  return 0
}

# --- Task queue ---
#
# Arrays indexed by task number:
#   TASK_TARGETS[i]  = "name|github|lang|reference"
#   TASK_FLAGS[i]    = "--skip-analysis ..." (optional)
#   TASK_PROMPTS[i]  = path to prompt file (optional)

TASK_TARGETS=()
TASK_FLAGS=()

load_queue() {
  [[ -f "$QUEUE_FILE" ]] || { log "Queue file not found: $QUEUE_FILE"; exit 1; }

  while IFS= read -r line; do
    [[ -z "${line// /}" || "$line" =~ ^[[:space:]]*# ]] && continue
    local target flags=""
    # Split on first tab: target<TAB>flags
    if [[ "$line" == *$'\t'* ]]; then
      target="${line%%$'\t'*}"
      flags="${line#*$'\t'}"
      # Strip leading tabs from flags
      flags="${flags#"${flags%%[!$'\t']*}"}"
    else
      target="$line"
    fi
    TASK_TARGETS+=("$target")
    TASK_FLAGS+=("$flags")
  done < "$QUEUE_FILE"
  log "Loaded ${#TASK_TARGETS[@]} tasks from $QUEUE_FILE"
}

# --- Setup: clone repo + write .prompt-extra.md ---

setup_task() {
  local idx="$1"
  local target="${TASK_TARGETS[$idx]}"
  local name github lang
  IFS='|' read -r name github lang _ <<< "$target"

  local work_dir="$SPECULA_ROOT/case-studies/$name"
  mkdir -p "$work_dir/spec" "$work_dir/artifact"

  # Clone repo if not present
  local repo_name="${github##*/}"
  local artifact_dir="$work_dir/artifact/$repo_name"
  if [[ ! -d "$artifact_dir/.git" && ! -f "$artifact_dir/.git" ]]; then
    log "CLONE $name: github.com/$github -> $artifact_dir"
    if $DRY_RUN; then
      log "DRY-RUN: git clone --depth 1 https://github.com/$github $artifact_dir"
    else
      git clone --depth 1 "https://github.com/$github" "$artifact_dir" 2>&1 | tail -1
    fi
  fi

  # Write .prompt-extra.md if --prompt specified
  if [[ -n "$PROMPT_FILE" && -f "$PROMPT_FILE" ]]; then
    if $DRY_RUN; then
      log "DRY-RUN: cp $PROMPT_FILE -> $work_dir/.prompt-extra.md"
    else
      cp "$PROMPT_FILE" "$work_dir/.prompt-extra.md"
      log "PROMPT $name: wrote .prompt-extra.md"
    fi
  fi
}

# --- Worker ---

run_task() {
  local idx="$1"
  local target="${TASK_TARGETS[$idx]}"
  local flags="${TASK_FLAGS[$idx]}"
  local name="${target%%|*}"
  local task_log="$LOG_DIR/${name}.log"

  # Setup first (clone + prompt)
  setup_task "$idx"

  log "START #$((idx+1)) $name"
  echo "running" > "$LOG_DIR/status/$idx"

  local -a cmd=(bash "$SPECULA_ROOT/scripts/launch/launch_pipeline.sh")
  if [[ -n "$flags" ]]; then
    read -ra flag_arr <<< "$flags"
    cmd+=("${flag_arr[@]}")
  fi
  (( MAX_TURNS > 0 )) && cmd+=(--max-turns="$MAX_TURNS")
  cmd+=("$target")

  if $DRY_RUN; then
    log "DRY-RUN: ${cmd[*]}"
    echo "dry-run" > "$LOG_DIR/status/$idx"
    return 0
  fi

  local start_ts attempt max_retries=3
  for (( attempt=1; attempt<=max_retries; attempt++ )); do
    start_ts=$(date +%s)
    if "${cmd[@]}" > "$task_log" 2>&1; then
      local elapsed=$(( $(date +%s) - start_ts ))
      log "DONE  #$((idx+1)) $name  (success, ${elapsed}s, attempt $attempt)"
      echo "success" > "$LOG_DIR/status/$idx"
      return 0
    fi

    local rc=$? elapsed=$(( $(date +%s) - start_ts ))

    # Check if failure was transient API error — retry after backoff
    local is_transient=false
    # API 500/529 in pipeline log
    if grep -q "API Error: 5[0-9][0-9]\|Internal server error\|overloaded_error\|Overloaded" "$task_log" 2>/dev/null; then
      is_transient=true
    fi
    # Agent produced no output (API failed before any work)
    local agent_log="$SPECULA_ROOT/case-studies/$name/agent.log"
    if [[ -f "$agent_log" ]] && grep -q "API Error:" "$agent_log" 2>/dev/null; then
      is_transient=true
    fi

    if $is_transient && (( attempt < max_retries )); then
      local backoff=$(( 180 * attempt ))
      log "RETRY #$((idx+1)) $name  (API error, attempt $attempt/$max_retries, backoff ${backoff}s)"
      sleep "$backoff"
      continue
    fi

    log "FAIL  #$((idx+1)) $name  (exit=$rc, ${elapsed}s, attempt $attempt)"
    echo "failed" > "$LOG_DIR/status/$idx"
    return 1
  done

  log "FAIL  #$((idx+1)) $name  (exhausted $max_retries retries)"
  echo "failed" > "$LOG_DIR/status/$idx"
}

# --- Main loop ---

main() {
  log "==========================================="
  log "Specula Scheduler  run=$RUN_ID"
  log "Workers=$WORKERS  Threshold=${THRESHOLD}%  MaxWindows=$MAX_WINDOWS"
  log "==========================================="

  load_queue
  (( ${#TASK_TARGETS[@]} == 0 )) && { log "Empty queue"; exit 0; }

  # Setup all tasks first (clone repos, write prompts)
  log "--- Setup phase ---"
  for (( i=0; i<${#TASK_TARGETS[@]}; i++ )); do
    setup_task "$i"
  done
  log "--- Setup complete ---"

  if $SETUP_ONLY; then
    log "Setup-only mode, exiting"
    exit 0
  fi

  local task_idx=0
  local -a pids=() pid_names=() pid_indices=()

  while (( task_idx < ${#TASK_TARGETS[@]} )) || (( ${#pids[@]} > 0 )); do

    # Reap finished workers
    local new_pids=() new_names=() new_indices=()
    for i in "${!pids[@]}"; do
      if kill -0 "${pids[$i]}" 2>/dev/null; then
        new_pids+=("${pids[$i]}")
        new_names+=("${pid_names[$i]}")
        new_indices+=("${pid_indices[$i]}")
      fi
    done
    pids=("${new_pids[@]+"${new_pids[@]}"}")
    pid_names=("${new_names[@]+"${new_names[@]}"}")
    pid_indices=("${new_indices[@]+"${new_indices[@]}"}")

    # Fill worker slots
    while (( ${#pids[@]} < WORKERS )) && (( task_idx < ${#TASK_TARGETS[@]} )); do
      if ! wait_for_quota; then
        log "Draining ${#pids[@]} active tasks..."
        for pid in "${pids[@]+"${pids[@]}"}"; do wait "$pid" 2>/dev/null || true; done
        pids=()
        break 2
      fi

      run_task "$task_idx" &
      local name="${TASK_TARGETS[$task_idx]%%|*}"
      pids+=($!)
      pid_names+=("$name")
      pid_indices+=("$task_idx")
      task_idx=$((task_idx + 1))
      sleep 3
    done

    sleep 30
  done

  # Final drain
  for pid in "${pids[@]+"${pids[@]}"}"; do wait "$pid" 2>/dev/null || true; done

  # --- Summary ---
  log "==========================================="
  log "SUMMARY"
  local total=${#TASK_TARGETS[@]} success=0 failed=0 other=0
  for (( i=0; i<total; i++ )); do
    local s name="${TASK_TARGETS[$i]%%|*}"
    s="$(cat "$LOG_DIR/status/$i" 2>/dev/null || echo "not-started")"
    case "$s" in
      success)  success=$((success+1)); log "  OK   $name" ;;
      failed)   failed=$((failed+1));   log "  FAIL $name" ;;
      dry-run)  log "  DRY  $name" ;;
      *)        other=$((other+1));     log "  ---- $name ($s)" ;;
    esac
  done
  log "Total=$total  Success=$success  Failed=$failed  Skipped=$other  Resets=$WINDOWS_USED"
  log "Logs: $LOG_DIR/"
  log "==========================================="
}

main
