#!/usr/bin/env bash
# Adapter: copilot-cli
# Capabilities: model-select, effort-select, auto-approve, background
# stop-gate: NOT supported — Copilot CLI has no stop-hook mechanism. The
# generic gate env vars (SPECULA_PHASE/SPECULA_WORK_DIR; see
# src/specula/stop_gate.py) are simply never read here, so the execution
# layer fails open by construction; the launcher-side acceptance audit
# still applies to runs through this adapter.
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
#   --claude-alias NAME    Accepted for adapter compatibility; ignored
#   --effort LEVEL         Reasoning effort; mapped to Copilot CLI's
#                          --reasoning-effort (requires Copilot CLI 1.0.4+)
#   --log output.log       Log file path (required)
#   --background           Run in background, print PID to stdout (default: foreground)
#   --help                 Show this help

set -euo pipefail

PROMPT=""
PROMPT_FILE=""
MAX_TURNS=""
MODEL="${COPILOT_MODEL:-}"
EFFORT=""
LOG_FILE=""
BACKGROUND=false

for arg in "$@"; do
  case "$arg" in
    --prompt=*)      PROMPT="${arg#*=}" ;;
    --prompt-file=*) PROMPT_FILE="${arg#*=}" ;;
    --max-turns=*)   MAX_TURNS="${arg#*=}" ;;
    --model=*)       MODEL="${arg#*=}" ;;
    --claude-alias=*) : ;;
    --effort=*)      EFFORT="${arg#*=}" ;;
    --log=*)         LOG_FILE="${arg#*=}" ;;
    --background)    BACKGROUND=true ;;
    --help|-h)
      sed -n '2,/^$/{ s/^# //; s/^#//; p }' "$0"
      exit 0
      ;;
    *) echo "copilot-cli adapter: unknown option: $arg" >&2; exit 1 ;;
  esac
done

# MODEL now carries the wrapper fallback or the explicit flag.  Always remove
# the environment variable before spawning Copilot so `--model=` can genuinely
# clear an inherited COPILOT_MODEL and return to settings.json / CLI defaults.
unset COPILOT_MODEL

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

# Probe optional CLI features once per adapter invocation.  Capability probing
# is more robust than parsing version strings across stable/prerelease channels.
COPILOT_HELP=""
COPILOT_HELP_READY=false
load_copilot_help() {
  if [[ "$COPILOT_HELP_READY" != true ]]; then
    COPILOT_HELP="$(copilot --help 2>&1 || true)"
    COPILOT_HELP_READY=true
  fi
}

# ── Build command ──
#
# Note: --background is handled by the caller (launch scripts use & directly).
# The adapter always runs the command in the foreground and redirects to log.
# Copilot CLI reads skills from project .github/skills/ or global ~/.agents/skills/.

CMD=(copilot -p "$PROMPT" --allow-all)

if [[ -n "$MODEL" ]]; then
  CMD+=(--model "$MODEL")
fi

if [[ -n "$EFFORT" ]]; then
  load_copilot_help
  if grep -q -- '--reasoning-effort' <<< "$COPILOT_HELP"; then
    CMD+=(--reasoning-effort "$EFFORT")
  elif grep -q -- '--effort' <<< "$COPILOT_HELP"; then
    # Short alias added after the canonical flag; retain this fallback for
    # unusual prerelease builds that advertise only the alias.
    CMD+=(--effort "$EFFORT")
  else
    echo "copilot-cli adapter: --effort requires Copilot CLI 1.0.4+ (installed client does not advertise --reasoning-effort)" >&2
    exit 1
  fi
fi

# Map --max-turns to --max-autopilot-continues (skip if 0 = unlimited)
if [[ -n "$MAX_TURNS" && "$MAX_TURNS" != "0" ]]; then
  CMD+=(--max-autopilot-continues "$MAX_TURNS")
fi

ACTIVITY_LOG="${SPECULA_ACTIVITY_LOG:-}"
if [[ -z "$ACTIVITY_LOG" ]]; then
  "${CMD[@]}" > "$LOG_FILE" 2>&1
  exit $?
fi

ADAPTER_DIR="$(cd -P "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
EVENT_HELPER="$ADAPTER_DIR/../../../src/specula/adapters/event_stream.py"

# JSON streaming arrived after the first Copilot CLI releases. Old clients
# still stream plain output through the helper without unsupported flags.
load_copilot_help
if grep -q -- '--output-format' <<< "$COPILOT_HELP"; then
  CMD+=(--output-format json)
fi
if grep -q -- '--stream' <<< "$COPILOT_HELP"; then
  CMD+=(--stream on)
fi

set +e
"${CMD[@]}" 2>&1 | python3 "$EVENT_HELPER" copilot "$ACTIVITY_LOG" "$LOG_FILE"
PIPELINE_STATUS=("${PIPESTATUS[@]}")
set -e

COPILOT_RC="${PIPELINE_STATUS[0]}"
STREAM_RC="${PIPELINE_STATUS[1]}"
if (( COPILOT_RC != 0 )); then
  exit "$COPILOT_RC"
fi
exit "$STREAM_RC"
