#!/usr/bin/env bash
# Adapter: codex
# Capabilities: max-turns, model-select, effort-select, auto-approve, background, stop-gate, resume
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
#   --claude-alias NAME    Accepted for launcher compatibility; ignored.
#   --model NAME           Model to use; passed to codex as -m. Env: CODEX_MODEL.
#                          Empty -> codex config.toml default.
#   --effort LEVEL         Reasoning effort (e.g. minimal|low|medium|high|ultra);
#                          passed as -c model_reasoning_effort. Env: CODEX_EFFORT.
#                          Empty -> codex config.toml default.
#   --resume-state PATH    Persist the exact Codex session ID and resume it when
#                          the state already contains one. Never selects --last.
#   --help                 Show this help

set -euo pipefail

PROMPT=""
PROMPT_FILE=""
MAX_TURNS=""
LOG_FILE=""
BACKGROUND=false
CLAUDE_ALIAS=""
RESUME_STATE=""
RESUME_STATE_SET=false
# Read adapter-specific environment defaults before parsing so an explicit
# empty flag can still win and clear them.
EFFORT="${CODEX_EFFORT:-}"
MODEL="${CODEX_MODEL:-}"
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
    --log=*)         LOG_FILE="${arg#*=}" ;;
    --background)    BACKGROUND=true ;;
    --claude-alias=*) CLAUDE_ALIAS="${arg#*=}" ;;
    --effort=*)      EFFORT="${arg#*=}" ;;
    --model=*)       MODEL="${arg#*=}" ;;
    --resume-state=*) RESUME_STATE="${arg#*=}"; RESUME_STATE_SET=true ;;
    --help|-h)
      sed -n '2,/^$/{ s/^# //; s/^#//; p }' "$0"
      exit 0
      ;;
    *) echo "codex adapter: unknown option: $arg" >&2; exit 1 ;;
  esac
done

# The resolved values are carried by argv below.  Do not leak the wrapper's
# fallback variables into Codex itself: an explicit `--model=` / `--effort=`
# must genuinely return to config.toml defaults.
unset CODEX_MODEL CODEX_EFFORT
unset SPECULA_RESUME_STATE SPECULA_RESUME_MODEL SPECULA_RESUME_EFFORT

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

if [[ "$RESUME_STATE_SET" == true && -z "$RESUME_STATE" ]]; then
  echo "codex adapter: --resume-state requires a path" >&2
  exit 1
fi

if [[ -n "$RESUME_STATE" && -d "$RESUME_STATE" ]]; then
  echo "codex adapter: --resume-state must be a file path: $RESUME_STATE" >&2
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

ADAPTER_DIR="$(cd -P "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SPECULA_SRC="$ADAPTER_DIR/../../../src"
RESUME_CWD="$(pwd -P)"
RESUME_SESSION_ID=""

read_resume_session_id() {
  python3 -I "$SPECULA_SRC/specula/adapters/utils/resume.py" read \
    "$RESUME_STATE" codex "$RESUME_CWD" "$MODEL" "$EFFORT"
}

if [[ -n "$RESUME_STATE" ]]; then
  if ! RESUME_SESSION_ID="$(read_resume_session_id)"; then
    echo "codex adapter: invalid or incompatible resume state: $RESUME_STATE" >&2
    exit 1
  fi
fi

# ── Run ──
#
# Note: Codex CLI currently does not expose a direct --max-turns flag for `exec`.
# We keep this option for adapter parity and rely on Codex defaults when running.

write_usage_file() {
  local log_file="$1"
  local sessions_dir="${CODEX_HOME:-$HOME/.codex}/sessions"
  local marker_file="$2"
  local usage_file="${log_file%.log}.usage.json"
  local write_rc=0
  local exact_session_id=""

  if [[ -n "$RESUME_STATE" ]]; then
    if ! exact_session_id="$(read_resume_session_id)"; then
      return 1
    fi
  fi

  python3 - <<'PY' "$usage_file" "$exact_session_id"
import json
import sys

with open(sys.argv[1], "w") as f:
    json.dump(
        {
            "agent": "codex",
            "session_id": sys.argv[2] or None,
            "session_file": None,
            "total_cost_usd": None,
            "usage": {},
        },
        f,
        indent=2,
    )
    f.write("\n")
PY
  write_rc=$?
  if (( write_rc != 0 )); then
    return "$write_rc"
  fi

  [[ -d "$sessions_dir" ]] || return 0

  local session_path=""
  if [[ -n "$RESUME_STATE" ]]; then
    # A resume-aware run is keyed exclusively by the ID captured from this
    # Codex stream. Never guess with a timestamp marker (or `--last`): another
    # concurrent Codex process may have written the newest rollout.
    [[ -n "$exact_session_id" ]] || return 0
    session_path="$(python3 - "$sessions_dir" "$exact_session_id" <<'PY'
import json
from pathlib import Path
import sys

sessions_dir = Path(sys.argv[1])
session_id = sys.argv[2]

# Normal Codex rollout filenames end in the thread UUID, which is both exact
# and cheap to locate. Fall back to the first session_meta record for layouts
# whose filename does not expose the ID.
for path in sorted(sessions_dir.rglob("rollout-*.jsonl")):
    if path.is_file() and path.name.endswith(f"-{session_id}.jsonl"):
        print(path)
        raise SystemExit(0)

for path in sorted(sessions_dir.rglob("rollout-*.jsonl")):
    try:
        with path.open(encoding="utf-8") as stream:
            first = json.loads(stream.readline())
    except (OSError, UnicodeError, json.JSONDecodeError):
        continue
    if first.get("type") != "session_meta":
        continue
    payload = first.get("payload")
    if isinstance(payload, dict) and payload.get("id") == session_id:
        print(path)
        raise SystemExit(0)
PY
    )"
  else
    session_path="$(
      find "$sessions_dir" -type f -name 'rollout-*.jsonl' -newer "$marker_file" 2>/dev/null \
      | sort \
      | tail -n1
    )"
  fi

  [[ -n "$session_path" ]] || return 0

  local session_file
  local session_id
  session_file="$(basename "$session_path" .jsonl)"
  if [[ -n "$RESUME_STATE" ]]; then
    session_id="$exact_session_id"
  else
    session_id="${session_path#${sessions_dir}/}"
    session_id="${session_id%.jsonl}"
  fi

  local ccusage_output=""
  if command -v npx >/dev/null 2>&1; then
    ccusage_output="$(
      npx @ccusage/codex@latest session --json 2>/dev/null \
      | python3 -c '
import json
import sys

session_file = sys.argv[1]
exact_session_id = sys.argv[2] or None

try:
    data = json.load(sys.stdin)
except Exception:
    sys.exit(1)

for session in data.get("sessions", []):
    if session.get("sessionFile") == session_file:
        json.dump(
            {
                "agent": "codex",
                "session_id": exact_session_id or session.get("sessionId"),
                "session_file": session.get("sessionFile"),
                "total_cost_usd": session.get("costUSD"),
                "usage": {
                    "input_tokens": session.get("inputTokens"),
                    "cached_input_tokens": session.get("cachedInputTokens"),
                    "output_tokens": session.get("outputTokens"),
                    "reasoning_output_tokens": session.get("reasoningOutputTokens"),
                    "total_tokens": session.get("totalTokens"),
                },
            },
            sys.stdout,
            indent=2,
        )
        print()
        sys.exit(0)

sys.exit(1)
' "$session_file" "$exact_session_id" 2>/dev/null
    )" || true
  fi

  if [[ -n "$ccusage_output" ]]; then
    printf '%s' "$ccusage_output" > "$usage_file"
    write_rc=$?
    return "$write_rc"
  fi

  python3 - <<'PY' "$usage_file" "$session_id" "$session_file"
import json
import sys

with open(sys.argv[1], "w") as f:
    json.dump(
        {
            "agent": "codex",
            "session_id": sys.argv[2],
            "session_file": sys.argv[3],
            "total_cost_usd": None,
            "usage": {},
        },
        f,
        indent=2,
    )
    f.write("\n")
PY
  write_rc=$?
  return "$write_rc"
}

run_codex() {
  local log_file="$1"
  local last_message_file="${log_file%.log}.last-message.txt"
  local marker_file
  local activity_log="${SPECULA_ACTIVITY_LOG:-}"
  local temporary_activity_log=""
  local adapter_dir
  local specula_src
  adapter_dir="$(cd -P "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
  specula_src="$adapter_dir/../../../src"
  marker_file="$(mktemp)"
  if [[ -n "$RESUME_STATE" && -z "$activity_log" ]]; then
    if ! temporary_activity_log="$(mktemp "${TMPDIR:-/tmp}/specula-codex-activity-XXXXXX.jsonl")"; then
      rm -f "$marker_file" || true
      echo "codex adapter: unable to create temporary activity log for session capture" >&2
      return 1
    fi
    # Native resume requires the exact thread.started ID. Keep JSON streaming
    # enabled even when the user disables progress display; the temporary raw
    # sidecar is removed below and does not opt the UI back into progress.
    activity_log="$temporary_activity_log"
  fi

  # ── Optional outer srt sandbox (M1.3) ──
  # Opt-in via SPECULA_SANDBOX=on; additive — off/unset leaves the codex argv
  # byte-for-byte. One outer layer wraps codex and every descendant (TLC/MCP/
  # build); the inner --dangerously-bypass-approvals-and-sandbox stays (YOLO,
  # no nested second sandbox). Backend path repo-relative, overridable.
  local -a cmd=()
  if [[ "${SPECULA_SANDBOX:-}" == "on" ]]; then
    local backend
    backend="${SPECULA_SANDBOX_BACKEND:-$adapter_dir/../sandbox/backend.mjs}"
    cmd+=(node "$backend" --workspace "${SPECULA_WORK_DIR:-$PWD}")
    [[ -n "${SPECULA_SANDBOX_CONFIG:-}" ]] && cmd+=(--config "$SPECULA_SANDBOX_CONFIG")
    cmd+=(--)
  fi
  # Feed the prompt via stdin (`-`), never as one argv element: Linux caps a
  # single argument at MAX_ARG_STRLEN, while confirmation/debate prompts can be
  # substantially larger. Preserve the activity stream and the Codex exit code
  # added by the progress lifecycle work.
  cmd+=(codex exec --dangerously-bypass-approvals-and-sandbox --output-last-message "$last_message_file")
  # Keep one large tool result from jumping past Codex's auto-compaction point.
  cmd+=(-c "tool_output_token_limit=10000")
  # Model / reasoning effort (additive — empty leaves codex config.toml default).
  [[ -n "$MODEL" ]] && cmd+=(-m "$MODEL")
  [[ -n "$EFFORT" ]] && cmd+=(-c "model_reasoning_effort=$EFFORT")
  if [[ -n "$RESUME_SESSION_ID" ]]; then
    cmd+=(resume "$RESUME_SESSION_ID")
  fi

  local codex_rc=0
  local transient_classified=false
  # Never let a failed/retried turn reuse the preceding turn's answer.
  rm -f "$last_message_file"
  set +e
  if [[ -n "$activity_log" ]]; then
    local -a pipeline_status
    local -a stream_args=(codex "$activity_log" "$log_file")
    local stream_rc
    if [[ -n "$RESUME_STATE" ]]; then
      stream_args+=("$RESUME_STATE" "$RESUME_CWD" "$MODEL" "$EFFORT")
    fi
    printf '%s' "$PROMPT" | "${cmd[@]}" --json - 2>&1 | python3 -I -c \
      'import sys; sys.path.insert(0, sys.argv.pop(1)); from specula.adapters.utils.event_stream import main; raise SystemExit(main(sys.argv[1:]))' \
      "$specula_src" "${stream_args[@]}"
    pipeline_status=("${PIPESTATUS[@]}")
    codex_rc="${pipeline_status[1]}"
    stream_rc="${pipeline_status[2]}"
    if (( stream_rc == RESUME_STATE_FAILURE_RC )); then
      # Session-integrity failure is fail-closed even when the native CLI also
      # reports a retryable status. Never resume a state whose exact ID changed.
      codex_rc=1
    elif (( codex_rc == 75 || stream_rc == 75 )); then
      codex_rc=75  # Rate limiting remains the highest-priority retry outcome.
    elif (( stream_rc == POLICY_BLOCKED_RC )); then
      codex_rc="$POLICY_BLOCKED_RC"
    elif (( codex_rc == POLICY_BLOCKED_RC )); then
      : # Preserve an already-normalized policy outcome over transient status.
    elif (( codex_rc != 0 && stream_rc == PLAIN_POLICY_DIAGNOSTIC_RC )); then
      codex_rc="$POLICY_BLOCKED_RC"
    elif (( stream_rc == TRANSIENT_FAILURE_RC )); then
      # A structured provider envelope is authoritative over an ordinary CLI
      # failure (and over an accidental zero exit), but not over 75/76 above.
      codex_rc="$TRANSIENT_FAILURE_RC"
      transient_classified=true
    elif (( codex_rc != 0 && stream_rc == PLAIN_TRANSIENT_DIAGNOSTIC_RC )); then
      codex_rc="$TRANSIENT_FAILURE_RC"
      transient_classified=true
    elif (( codex_rc == 0 )); then
      # A plain diagnostic is only actionable when the CLI itself failed.
      # Structured policy failures use POLICY_BLOCKED_RC above and remain
      # authoritative even if a provider CLI accidentally exits zero.
      if (( stream_rc != PLAIN_POLICY_DIAGNOSTIC_RC \
            && stream_rc != PLAIN_TRANSIENT_DIAGNOSTIC_RC )); then
        codex_rc="$stream_rc"
      fi
    fi
  else
    local -a pipeline_status
    printf '%s' "$PROMPT" | "${cmd[@]}" - > "$log_file" 2>&1
    pipeline_status=("${PIPESTATUS[@]}")
    codex_rc="${pipeline_status[1]}"
  fi
  set -e

  if [[ -z "$activity_log" ]] && (( codex_rc != 0 && codex_rc != 75 )); then
    # Without progress streaming there is no structured event status. Only
    # classify an already-failed CLI's diagnostic log; successful agent output
    # may quote an old policy message and must remain successful.
    if python3 -I -c \
      'import sys; sys.path.insert(0, sys.argv[1]); from pathlib import Path; from specula.adapters.utils.policy import failed_log_has_policy_block; raise SystemExit(0 if failed_log_has_policy_block(Path(sys.argv[2])) else 1)' \
      "$specula_src" "$log_file"; then
      codex_rc="$POLICY_BLOCKED_RC"
    elif (( codex_rc != POLICY_BLOCKED_RC )) && python3 -I -c \
      'import sys; sys.path.insert(0, sys.argv[1]); from pathlib import Path; from specula.adapters.utils.transient import failed_log_has_transient_failure; raise SystemExit(0 if failed_log_has_transient_failure(Path(sys.argv[2])) else 1)' \
      "$specula_src" "$log_file"; then
      codex_rc="$TRANSIENT_FAILURE_RC"
      transient_classified=true
    fi
  fi

  if (( codex_rc == TRANSIENT_FAILURE_RC )) && [[ "$transient_classified" != true ]]; then
    # Native 74 is EX_IOERR; only a classified provider diagnostic may expose
    # Specula's retry/resume contract to the phase runner.
    codex_rc=1
  fi

  if [[ -n "$temporary_activity_log" ]]; then
    rm -f "$temporary_activity_log" || true
  fi

  local usage_rc=0
  write_usage_file "$log_file" "$marker_file" || usage_rc=$?
  rm -f "$marker_file" || true
  if (( codex_rc != 0 )); then
    return "$codex_rc"
  fi
  return "$usage_rc"
}

# ── Stop gate (execution layer) ──
# Generic gate interface: the phase launcher exports SPECULA_PHASE +
# SPECULA_WORK_DIR (see src/specula/stop_gate.py). Parallel workers may narrow
# gate state/PID scanning with SPECULA_STOP_GATE_WORK_DIR. Codex discovers
# hooks from the project layer (<git toplevel of cwd>/.codex/hooks.json), so arm
# the gate by writing a Stop hook there; per-run specifics travel via env, so the file
# content is identical for every run. A hooks.json THIS run created is removed
# again on exit (an EXIT trap), so foreign checkouts are not left polluted; a
# pre-existing foreign hooks.json is never touched — the gate disarms with a
# warning instead (the launcher-side acceptance audit still applies). Known
# limitation: concurrent codex agents sharing one toplevel race that cleanup
# (hooks are read at codex startup, so running agents are unaffected).
#
# The whole block is fail-open: under this script's `set -e`, any setup
# failure (no python3, read-only fs) must disarm the gate with a warning,
# never kill the adapter before codex even starts.
GATE_WORK_DIR="${SPECULA_STOP_GATE_WORK_DIR:-${SPECULA_WORK_DIR:-}}"
if [[ -n "${SPECULA_PHASE:-}" && -n "${SPECULA_WORK_DIR:-}" \
      && "${SPECULA_STOP_GATE:-on}" != "off" && -d "${SPECULA_WORK_DIR:-}" \
      && -d "$GATE_WORK_DIR" ]]; then
  ADAPTER_DIR="$(cd -P "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
  GATE_PY="$ADAPTER_DIR/../../../src/specula/stop_gate.py"
  HOOKS_ROOT="$(git rev-parse --show-toplevel 2>/dev/null || pwd)"
  HOOKS_FILE="$HOOKS_ROOT/.codex/hooks.json"
  HOOKS_PREEXISTED=false
  [[ -e "$HOOKS_FILE" ]] && HOOKS_PREEXISTED=true
  {
    python3 "$GATE_PY" reset "$GATE_WORK_DIR" &&   # fresh fuse per agent run
    if ! $HOOKS_PREEXISTED; then
      mkdir -p "$HOOKS_ROOT/.codex" &&
      printf '{\n  "hooks": {\n    "Stop": [\n      { "hooks": [ { "type": "command", "command": "python3 %s codex", "timeout": 60 } ] }\n    ]\n  }\n}\n' \
        "'$GATE_PY'" > "$HOOKS_FILE"
    elif ! grep -q "stop_gate.py" "$HOOKS_FILE" 2>/dev/null; then
      echo "codex adapter: $HOOKS_FILE exists without the stop gate; leaving it untouched (gate disarmed for this run)" >&2
    fi
  } || echo "codex adapter: stop-gate setup failed; continuing without the gate" >&2
  if ! $HOOKS_PREEXISTED && [[ -e "$HOOKS_FILE" ]]; then
    trap 'rm -f "$HOOKS_FILE" 2>/dev/null; rmdir "$HOOKS_ROOT/.codex" 2>/dev/null || true' EXIT
  fi
fi

# Launch scripts already background the adapter process when they pass
# --background, matching the claude-code adapter. Keep the Codex process in
# this adapter's foreground so the parent can wait on the real work.
run_codex "$LOG_FILE"
