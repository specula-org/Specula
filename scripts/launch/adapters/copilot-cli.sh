#!/usr/bin/env bash
# Adapter: copilot-cli
# Capabilities: model-select, effort-select, auto-approve, autopilot, background
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
#   --resume-state PATH    Persist/resume the exact native Copilot session
#   --background           Run in background, print PID to stdout (default: foreground)
#   --help                 Show this help

set -euo pipefail

PROMPT=""
PROMPT_FILE=""
MAX_TURNS=""
MODEL="${COPILOT_MODEL:-}"
EFFORT=""
LOG_FILE=""
RESUME_STATE=""
RESUME_STATE_SET=false
BACKGROUND=false
POLICY_BLOCKED_RC=76  # Keep in sync with src/specula/adapters/utils/policy.py.
PLAIN_POLICY_DIAGNOSTIC_RC=77  # Internal event-stream candidate; never returned to the runner.
TRANSIENT_FAILURE_RC=74  # Keep in sync with src/specula/adapters/utils/transient.py.
PLAIN_TRANSIENT_DIAGNOSTIC_RC=78  # Internal event-stream candidate; never returned to the runner.
RESUME_STATE_FAILURE_RC=79  # Internal event-stream integrity failure; never returned to the runner.

for arg in "$@"; do
  case "$arg" in
    --prompt=*)      PROMPT="${arg#*=}" ;;
    --prompt-file=*) PROMPT_FILE="${arg#*=}" ;;
    --max-turns=*)   MAX_TURNS="${arg#*=}" ;;
    --model=*)       MODEL="${arg#*=}" ;;
    --claude-alias=*) : ;;
    --effort=*)      EFFORT="${arg#*=}" ;;
    --log=*)         LOG_FILE="${arg#*=}" ;;
    --resume-state=*) RESUME_STATE="${arg#*=}"; RESUME_STATE_SET=true ;;
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
unset SPECULA_RESUME_STATE SPECULA_RESUME_MODEL SPECULA_RESUME_EFFORT

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

if [[ "$RESUME_STATE_SET" == true && -z "$RESUME_STATE" ]]; then
  echo "copilot-cli adapter: --resume-state requires a path" >&2
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

# ── Guard prompt size ──
#
# Unlike codex (stdin) and claude-code (stdin), the copilot CLI accepts the
# prompt ONLY as a command-line argument (-p <text>) — it exposes no stdin or
# prompt-file input. A single argv argument is capped at MAX_ARG_STRLEN (128 KiB
# on Linux), so an oversized prompt (e.g. a debate turn embedding a prior
# transcript) would otherwise fail deep in exec with a cryptic "Argument list
# too long" and no output. Fail loudly and early, and steer to an agent that can
# take large prompts. (printf is a bash builtin, so measuring is not itself
# subject to ARG_MAX.)
PROMPT_BYTES=$(printf '%s' "$PROMPT" | wc -c)
MAX_PROMPT_BYTES=124000
if (( PROMPT_BYTES > MAX_PROMPT_BYTES )); then
  ERROR="copilot-cli adapter: prompt is ${PROMPT_BYTES} bytes, over the ~${MAX_PROMPT_BYTES}-byte limit the copilot CLI accepts as a command-line argument (it has no stdin/prompt-file input). Use --agent=codex or --agent=claude-code for large-context or --debate prompts."
  printf '%s\n' "$ERROR" >&2
  if ! printf '%s\n' "$ERROR" > "$LOG_FILE"; then
    printf 'copilot-cli adapter: unable to write diagnostic log: %s\n' "$LOG_FILE" >&2
  fi
  exit 1
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

ADAPTER_DIR="$(cd -P "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SPECULA_SRC="$ADAPTER_DIR/../../../src"

# ── Build command ──
#
# Note: --background is handled by the caller (launch scripts use & directly).
# The adapter always runs the command in the foreground and redirects to log.
# Copilot CLI reads skills from project .github/skills/ or global ~/.agents/skills/.

load_copilot_help
if ! grep -q -- '--autopilot' <<< "$COPILOT_HELP"; then
  echo "copilot-cli adapter: autonomous execution requires --autopilot, but the installed Copilot CLI does not advertise it; upgrade Copilot CLI" >&2
  exit 1
fi

RESUME_SESSION_ID=""
if [[ -n "$RESUME_STATE" ]]; then
  if ! grep -q -- '--output-format' <<< "$COPILOT_HELP"; then
    echo "copilot-cli adapter: --resume-state requires Copilot CLI JSON output so the exact session ID can be captured; upgrade Copilot CLI" >&2
    exit 1
  fi
  if ! grep -q -- '--resume' <<< "$COPILOT_HELP" || ! grep -q -- '--session-id' <<< "$COPILOT_HELP"; then
    echo "copilot-cli adapter: --resume-state requires Copilot CLI 1.0.51+ exact-session resume semantics; upgrade Copilot CLI" >&2
    exit 1
  fi
  if ! RESUME_SESSION_ID="$(python3 -I "$SPECULA_SRC/specula/adapters/utils/resume.py" read \
    "$RESUME_STATE" copilot-cli "$(pwd -P)" "$MODEL" "$EFFORT")"; then
    exit 1
  fi
fi

# Keep the scripting channel free of version-specific stats footers. Provider
# diagnostics still go to stderr, which is captured below for policy recovery.
CMD=(copilot -p "$PROMPT" --allow-all --autopilot --silent)

if [[ -n "$RESUME_SESSION_ID" ]]; then
  if [[ ! "$RESUME_SESSION_ID" =~ ^[0-9A-Fa-f]{8}-[0-9A-Fa-f]{4}-[0-9A-Fa-f]{4}-[0-9A-Fa-f]{4}-[0-9A-Fa-f]{12}$ ]]; then
    echo "copilot-cli adapter: saved session ID is not a full UUID; refusing ambiguous resume" >&2
    exit 1
  fi
  # --session-id creates a blank session when a UUID no longer exists. A full
  # UUID passed to --resume instead fails when no stored session matches, so a
  # stale state can never receive a context-free continuation prompt.
  CMD+=(--resume "$RESUME_SESSION_ID")
fi

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
TEMP_ACTIVITY_LOG=""
if [[ -n "$RESUME_STATE" && -z "$ACTIVITY_LOG" ]]; then
  if ! TEMP_ACTIVITY_LOG="$(mktemp "${TMPDIR:-/tmp}/specula-copilot-activity-XXXXXX.jsonl")"; then
    echo "copilot-cli adapter: unable to create temporary activity log for session capture" >&2
    exit 1
  fi
  ACTIVITY_LOG="$TEMP_ACTIVITY_LOG"
  trap 'rm -f -- "$TEMP_ACTIVITY_LOG"' EXIT
fi

failed_log_is_policy_blocked() {
  python3 -I -c \
    'import sys; sys.path.insert(0, sys.argv[1]); from pathlib import Path; from specula.adapters.utils.policy import failed_log_has_policy_block; raise SystemExit(0 if failed_log_has_policy_block(Path(sys.argv[2])) else 1)' \
    "$SPECULA_SRC" "$LOG_FILE"
}

failed_log_is_transient_failure() {
  python3 -I -c \
    'import sys; sys.path.insert(0, sys.argv[1]); from pathlib import Path; from specula.adapters.utils.transient import failed_log_has_transient_failure; raise SystemExit(0 if failed_log_has_transient_failure(Path(sys.argv[2])) else 1)' \
    "$SPECULA_SRC" "$LOG_FILE"
}

if [[ -z "$ACTIVITY_LOG" ]]; then
  set +e
  "${CMD[@]}" > "$LOG_FILE" 2>&1
  COPILOT_RC=$?
  set -e
  if (( COPILOT_RC == 75 )); then
    exit 75
  fi
  if (( COPILOT_RC == POLICY_BLOCKED_RC )); then
    exit "$POLICY_BLOCKED_RC"
  fi
  if (( COPILOT_RC != 0 )) && failed_log_is_policy_blocked; then
    exit "$POLICY_BLOCKED_RC"
  fi
  if (( COPILOT_RC != 0 )) && failed_log_is_transient_failure; then
    exit "$TRANSIENT_FAILURE_RC"
  fi
  if (( COPILOT_RC == TRANSIENT_FAILURE_RC )); then
    exit 1
  fi
  exit "$COPILOT_RC"
fi

# JSON streaming arrived after the first Copilot CLI releases. Old clients
# still stream plain output through the helper without unsupported flags.
load_copilot_help
COPILOT_JSON_STREAM=false
STREAM_ADAPTER=copilot
if grep -q -- '--output-format' <<< "$COPILOT_HELP"; then
  CMD+=(--output-format json)
  COPILOT_JSON_STREAM=true
  STREAM_ADAPTER=copilot-json
fi
if grep -q -- '--stream' <<< "$COPILOT_HELP"; then
  CMD+=(--stream on)
fi

set +e
STREAM_ARGS=("$STREAM_ADAPTER" "$ACTIVITY_LOG" "$LOG_FILE")
if [[ -n "$RESUME_STATE" ]]; then
  STREAM_ARGS+=("$RESUME_STATE" "$(pwd -P)" "$MODEL" "$EFFORT")
fi
"${CMD[@]}" 2>&1 | python3 -I -c \
  'import sys; sys.path.insert(0, sys.argv.pop(1)); from specula.adapters.utils.event_stream import main; raise SystemExit(main(sys.argv[1:]))' \
  "$SPECULA_SRC" "${STREAM_ARGS[@]}"
PIPELINE_STATUS=("${PIPESTATUS[@]}")
set -e

COPILOT_RC="${PIPELINE_STATUS[0]}"
STREAM_RC="${PIPELINE_STATUS[1]}"
if (( STREAM_RC == RESUME_STATE_FAILURE_RC )); then
  # Never let a retryable native exit mask a changed/malformed exact session.
  exit 1
fi
if (( COPILOT_RC == 75 )); then
  exit 75
fi
if (( STREAM_RC == 75 )); then
  exit 75
fi
if (( COPILOT_RC == POLICY_BLOCKED_RC )); then
  exit "$POLICY_BLOCKED_RC"
fi
if (( STREAM_RC == POLICY_BLOCKED_RC )); then
  exit "$POLICY_BLOCKED_RC"
fi
if (( COPILOT_RC != 0 && STREAM_RC == PLAIN_POLICY_DIAGNOSTIC_RC )); then
  exit "$POLICY_BLOCKED_RC"
fi
if (( STREAM_RC == TRANSIENT_FAILURE_RC )); then
  exit "$TRANSIENT_FAILURE_RC"
fi
if (( COPILOT_RC != 0 && STREAM_RC == PLAIN_TRANSIENT_DIAGNOSTIC_RC )); then
  exit "$TRANSIENT_FAILURE_RC"
fi
if (( COPILOT_RC != 0 )) && [[ "$COPILOT_JSON_STREAM" != true ]] && failed_log_is_policy_blocked; then
  exit "$POLICY_BLOCKED_RC"
fi
if (( COPILOT_RC != 0 )) && [[ "$COPILOT_JSON_STREAM" != true ]] && failed_log_is_transient_failure; then
  exit "$TRANSIENT_FAILURE_RC"
fi
if (( COPILOT_RC != 0 )); then
  if (( COPILOT_RC == TRANSIENT_FAILURE_RC )); then
    exit 1
  fi
  exit "$COPILOT_RC"
fi
if (( STREAM_RC == PLAIN_POLICY_DIAGNOSTIC_RC )); then
  exit 0
fi
if (( STREAM_RC == PLAIN_TRANSIENT_DIAGNOSTIC_RC )); then
  exit 0
fi
exit "$STREAM_RC"
