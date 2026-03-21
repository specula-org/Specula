#!/usr/bin/env bash
# Adapter: copilot-cli
# Capabilities: model-select, auto-approve, background
#
# Unified interface for invoking GitHub Copilot CLI.
#
# Usage:
#   scripts/launch/adapters/copilot-cli.sh [options]
#
# Options:
#   --prompt "..."         Task prompt (mutually exclusive with --prompt-file)
#   --prompt-file file.md  Read prompt from file (mutually exclusive with --prompt)
#   --max-turns N          Mapped to --max-autopilot-continues (0=unlimited, omits flag)
#   --model MODEL          AI model to use (default: $COPILOT_MODEL or Copilot CLI default)
#   --log output.log       Log file path (required)
#   --background           Run in background, print PID to stdout (default: foreground)
#   --help                 Show this help

set -euo pipefail

PROMPT=""
PROMPT_FILE=""
MAX_TURNS=""
MODEL="${COPILOT_MODEL:-}"
LOG_FILE=""
BACKGROUND=false

for arg in "$@"; do
  case "$arg" in
    --prompt=*)      PROMPT="${arg#*=}" ;;
    --prompt-file=*) PROMPT_FILE="${arg#*=}" ;;
    --max-turns=*)   MAX_TURNS="${arg#*=}" ;;
    --model=*)       MODEL="${arg#*=}" ;;
    --log=*)         LOG_FILE="${arg#*=}" ;;
    --background)    BACKGROUND=true ;;
    --help|-h)
      sed -n '2,/^$/{ s/^# //; s/^#//; p }' "$0"
      exit 0
      ;;
    *) echo "copilot-cli adapter: unknown option: $arg" >&2; exit 1 ;;
  esac
done

# ── Validate arguments ──

if [[ -n "$PROMPT" && -n "$PROMPT_FILE" ]]; then
  echo "copilot-cli adapter: --prompt and --prompt-file are mutually exclusive" >&2
  exit 1
fi

if [[ -z "$PROMPT" && -z "$PROMPT_FILE" ]]; then
  echo "copilot-cli adapter: one of --prompt or --prompt-file is required" >&2
  exit 1
fi

if [[ -z "$LOG_FILE" ]]; then
  echo "copilot-cli adapter: --log is required" >&2
  exit 1
fi

# ── Resolve prompt ──

if [[ -n "$PROMPT_FILE" ]]; then
  if [[ ! -f "$PROMPT_FILE" ]]; then
    echo "copilot-cli adapter: prompt file not found: $PROMPT_FILE" >&2
    exit 1
  fi
  PROMPT="$(cat "$PROMPT_FILE")"
fi

# ── Build command ──
#
# Note: --background is handled by the caller (launch scripts use & directly).
# The adapter always runs the command in the foreground and redirects to log.
# Copilot CLI reads skills from .github/skills/ in the repo root.

CMD=(copilot -p "$PROMPT" --allow-all)

if [[ -n "$MODEL" ]]; then
  CMD+=(--model "$MODEL")
fi

# Map --max-turns to --max-autopilot-continues (skip if 0 = unlimited)
if [[ -n "$MAX_TURNS" && "$MAX_TURNS" != "0" ]]; then
  CMD+=(--max-autopilot-continues "$MAX_TURNS")
fi

"${CMD[@]}" > "$LOG_FILE" 2>&1
