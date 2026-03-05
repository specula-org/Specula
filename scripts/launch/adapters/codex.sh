#!/usr/bin/env bash
# Adapter: codex
# Capabilities: max-turns, auto-approve, background
#
# Unified interface for invoking Codex CLI.
#
# Usage:
#   scripts/launch/adapters/codex.sh [options]
#
# Options:
#   --prompt "..."         Task prompt (mutually exclusive with --prompt-file)
#   --prompt-file file.md  Read prompt from file (mutually exclusive with --prompt)
#   --max-turns N          Max iterations, 0=unlimited (required) (Not currently supported with Codex, https://github.com/openai/codex/issues/12336)
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
    *) echo "codex adapter: unknown option: $arg" >&2; exit 1 ;;
  esac
done

# ── Validate arguments ──

if [[ -n "$PROMPT" && -n "$PROMPT_FILE" ]]; then
  echo "codex adapter: --prompt and --prompt-file are mutually exclusive" >&2
  exit 1
fi

if [[ -z "$PROMPT" && -z "$PROMPT_FILE" ]]; then
  echo "codex adapter: one of --prompt or --prompt-file is required" >&2
  exit 1
fi

if [[ -z "$MAX_TURNS" ]]; then
  echo "codex adapter: --max-turns is required" >&2
  exit 1
fi

if [[ -z "$LOG_FILE" ]]; then
  echo "codex adapter: --log is required" >&2
  exit 1
fi

# ── Resolve prompt ──

if [[ -n "$PROMPT_FILE" ]]; then
  if [[ ! -f "$PROMPT_FILE" ]]; then
    echo "codex adapter: prompt file not found: $PROMPT_FILE" >&2
    exit 1
  fi
  PROMPT="$(cat "$PROMPT_FILE")"
fi

# ── Run ──
#
# Note: Codex CLI currently does not expose a direct --max-turns flag for `exec`.
# We keep this option for adapter parity and rely on Codex defaults when running.

if $BACKGROUND; then
  nohup codex exec \
    --dangerously-bypass-approvals-and-sandbox \
    "$PROMPT" \
    > "$LOG_FILE" 2>&1 &
  echo $!
else
  codex exec \
    --dangerously-bypass-approvals-and-sandbox \
    "$PROMPT" \
    > "$LOG_FILE" 2>&1
fi
