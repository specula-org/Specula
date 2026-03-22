#!/usr/bin/env bash
# Adapter: claude-code
# Capabilities: max-turns, mcp, auto-approve, background
#
# Unified interface for invoking Claude Code CLI.
#
# Usage:
#   scripts/launch/adapters/claude-code.sh [options]
#
# Options:
#   --prompt "..."         Task prompt (mutually exclusive with --prompt-file)
#   --prompt-file file.md  Read prompt from file (mutually exclusive with --prompt)
#   --max-turns N          (DEPRECATED, ignored — use --max-budget)
#   --max-budget N         Max dollar budget for API calls (optional)
#   --log output.log       Log file path (required)
#   --background           Run in background, print PID to stdout (default: foreground)
#   --help                 Show this help

set -euo pipefail

PROMPT=""
PROMPT_FILE=""
MAX_TURNS=""
MAX_BUDGET=""
LOG_FILE=""
BACKGROUND=false

for arg in "$@"; do
  case "$arg" in
    --prompt=*)      PROMPT="${arg#*=}" ;;
    --prompt-file=*) PROMPT_FILE="${arg#*=}" ;;
    --max-turns=*)   MAX_TURNS="${arg#*=}" ;;  # deprecated, ignored
    --max-budget=*)  MAX_BUDGET="${arg#*=}" ;;
    --log=*)         LOG_FILE="${arg#*=}" ;;
    --background)    BACKGROUND=true ;;
    --help|-h)
      sed -n '2,/^$/{ s/^# //; s/^#//; p }' "$0"
      exit 0
      ;;
    *) echo "claude-code adapter: unknown option: $arg" >&2; exit 1 ;;
  esac
done

# ── Validate arguments ──

if [[ -n "$PROMPT" && -n "$PROMPT_FILE" ]]; then
  echo "claude-code adapter: --prompt and --prompt-file are mutually exclusive" >&2
  exit 1
fi

if [[ -z "$PROMPT" && -z "$PROMPT_FILE" ]]; then
  echo "claude-code adapter: one of --prompt or --prompt-file is required" >&2
  exit 1
fi

if [[ -z "$LOG_FILE" ]]; then
  echo "claude-code adapter: --log is required" >&2
  exit 1
fi

# ── Resolve prompt ──
# Feed prompt via stdin (not -p) to keep the process cmdline clean.
# This prevents pkill -f collateral kills when the prompt contains
# strings like "tlc2.TLC" that match other processes.

if [[ -n "$PROMPT_FILE" ]]; then
  if [[ ! -f "$PROMPT_FILE" ]]; then
    echo "claude-code adapter: prompt file not found: $PROMPT_FILE" >&2
    exit 1
  fi
  PROMPT_INPUT="$PROMPT_FILE"
else
  # Write inline prompt to temp file
  PROMPT_INPUT="$(mktemp)"
  echo "$PROMPT" > "$PROMPT_INPUT"
  trap "rm -f '$PROMPT_INPUT'" EXIT
fi

# ── Environment setup ──

unset CLAUDECODE 2>/dev/null || true
unset CLAUDE_CODE_SSE_PORT 2>/dev/null || true
unset CLAUDE_CODE_ENTRYPOINT 2>/dev/null || true

# ── Build command ──

CMD=(claude --print --dangerously-skip-permissions --output-format json)

# Budget control
if [[ -n "$MAX_BUDGET" && "$MAX_BUDGET" != "0" ]]; then
  CMD+=(--max-budget-usd "$MAX_BUDGET")
fi

# ── Run ──
# Write JSON output to raw file, then post-process into .log and .usage.json
RAW_JSON="${LOG_FILE%.log}.raw.json"

"${CMD[@]}" < "$PROMPT_INPUT" > "$RAW_JSON" 2>&1 || true

# Extract the text result for human-readable log
python3 -c "
import json, sys
try:
    with open(sys.argv[1]) as f:
        d = json.load(f)
    print(d.get('result', ''))
except:
    # If JSON parse fails, the raw output is plain text (e.g., error message)
    with open(sys.argv[1]) as f:
        print(f.read())
" "$RAW_JSON" > "$LOG_FILE"

# Extract usage stats
python3 -c "
import json, sys
try:
    with open(sys.argv[1]) as f:
        d = json.load(f)
    usage = {
        'total_cost_usd': d.get('total_cost_usd', 0),
        'num_turns': d.get('num_turns', 0),
        'duration_ms': d.get('duration_ms', 0),
        'stop_reason': d.get('stop_reason', ''),
        'usage': d.get('usage', {}),
        'model_usage': d.get('modelUsage', {})
    }
    json.dump(usage, sys.stdout, indent=2)
    print()
except:
    json.dump({'error': 'parse_failed'}, sys.stdout)
    print()
" "$RAW_JSON" > "${LOG_FILE%.log}.usage.json"
