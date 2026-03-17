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
#   --max-turns N          Max agent turns, 0=unlimited (optional)
#   --log output.log       Log file path (required)
#   --background           Run in background, print PID to stdout (default: foreground)
#   --help                 Show this help

set -euo pipefail

PROMPT=""
PROMPT_FILE=""
MAX_TURNS=""
LOG_FILE=""
BACKGROUND=false

for arg in "$@"; do
  case "$arg" in
    --prompt=*)      PROMPT="${arg#*=}" ;;
    --prompt-file=*) PROMPT_FILE="${arg#*=}" ;;
    --max-turns=*)   MAX_TURNS="${arg#*=}" ;;
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

if [[ -n "$PROMPT_FILE" ]]; then
  if [[ ! -f "$PROMPT_FILE" ]]; then
    echo "claude-code adapter: prompt file not found: $PROMPT_FILE" >&2
    exit 1
  fi
  PROMPT="$(cat "$PROMPT_FILE")"
fi

# ── Environment setup ──

unset CLAUDECODE 2>/dev/null || true
unset CLAUDE_CODE_SSE_PORT 2>/dev/null || true
unset CLAUDE_CODE_ENTRYPOINT 2>/dev/null || true

# ── Build command ──

CMD=(claude --print --dangerously-skip-permissions)

# Only pass --max-turns if set and non-zero (0 = unlimited = don't pass flag)
if [[ -n "$MAX_TURNS" && "$MAX_TURNS" != "0" ]]; then
  CMD+=(--max-turns "$MAX_TURNS")
fi

CMD+=(-p "$PROMPT")

# ── Run ──
# Note: --background is handled by the caller (launch scripts use & directly).
# The adapter always runs the command in the foreground and redirects to log.

"${CMD[@]}" > "$LOG_FILE" 2>&1
