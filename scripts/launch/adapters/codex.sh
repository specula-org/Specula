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
  local exact_session_id="$2"
  local sessions_dir="${CODEX_HOME:-$HOME/.codex}/sessions"
  local usage_file="${log_file%.log}.usage.json"
  local write_rc=0

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

  if [[ -z "$exact_session_id" ]]; then
    echo "codex adapter: usage unavailable: exact thread.started ID was not captured" >&2
    return 0
  fi

  if [[ ! -d "$sessions_dir" ]]; then
    echo "codex adapter: usage unavailable: sessions directory not found: $sessions_dir" >&2
    return 0
  fi

  local session_path=""
  # Every run is keyed exclusively by the documented thread.started ID from
  # this Codex stream. Never guess with timestamps (or `--last`): another
  # concurrent Codex process may be creating or resuming a rollout.
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

  if [[ -z "$session_path" ]]; then
    echo "codex adapter: usage unavailable: session $exact_session_id was not found" >&2
    return 0
  fi

  local session_file
  session_file="$(basename "$session_path" .jsonl)"

  local ccusage_output=""
  if command -v npx >/dev/null 2>&1; then
    if ! ccusage_output="$(
      npx --yes ccusage@20.0.19 codex session --json 2>/dev/null \
      | python3 -c '
import json
import math
from pathlib import Path
import sys

root_session_file = sys.argv[1]
exact_session_id = sys.argv[2]
sessions_dir = Path(sys.argv[3])

try:
    data = json.load(sys.stdin)
except Exception:
    sys.exit(1)

parents = {}
files_by_id = {}
for path in sorted(sessions_dir.rglob("rollout-*.jsonl")):
    try:
        if not path.is_file():
            continue
        with path.open(encoding="utf-8") as stream:
            first = json.loads(stream.readline())
    except (OSError, UnicodeError, json.JSONDecodeError):
        continue
    if first.get("type") != "session_meta":
        continue
    payload = first.get("payload")
    if not isinstance(payload, dict):
        continue
    session_id = payload.get("id") or payload.get("session_id")
    if not isinstance(session_id, str) or not session_id:
        continue
    files_by_id[session_id] = path.stem
    parent_id = payload.get("parent_thread_id")
    source = payload.get("source")
    subagent = source.get("subagent") if isinstance(source, dict) else None
    if parent_id is None and isinstance(subagent, dict):
        thread_spawn = subagent.get("thread_spawn")
        if isinstance(thread_spawn, dict):
            parent_id = thread_spawn.get("parent_thread_id")
        if parent_id is None:
            parent_id = payload.get("forked_from_id")
    if isinstance(parent_id, str) and parent_id:
        parents[session_id] = parent_id

included_ids = {exact_session_id}
changed = True
while changed:
    changed = False
    for child_id, parent_id in parents.items():
        if parent_id in included_ids and child_id not in included_ids:
            included_ids.add(child_id)
            changed = True

target_files = {root_session_file}
target_files.update(files_by_id[session_id] for session_id in included_ids if session_id in files_by_id)

sessions = data.get("sessions")
if not isinstance(sessions, list):
    sys.exit(1)
rows_by_file = {}
for session in sessions:
    if not isinstance(session, dict):
        sys.exit(1)
    session_file = session.get("sessionFile")
    if not isinstance(session_file, str) or not session_file:
        continue
    if session_file in rows_by_file:
        sys.exit(1)
    rows_by_file[session_file] = session

root = rows_by_file.get(root_session_file)
if root is None:
    sys.exit(1)
if not target_files.issubset(rows_by_file):
    sys.exit(1)
selected = [rows_by_file[name] for name in sorted(target_files)]

def token_total(key, legacy_key=None, default=None):
    total = 0
    for row in selected:
        value = row.get(key)
        if value is None and legacy_key is not None:
            value = row.get(legacy_key)
        if value is None and default is not None:
            value = default
        if (
            isinstance(value, bool)
            or not isinstance(value, (int, float))
            or not math.isfinite(value)
            or value < 0
            or (isinstance(value, float) and not value.is_integer())
        ):
            raise ValueError(key)
        total += int(value)
    return total

costs = []
for row in selected:
    cost = row.get("costUSD")
    if isinstance(cost, bool) or not isinstance(cost, (int, float)) or not math.isfinite(cost) or cost < 0:
        sys.exit(1)
    costs.append(float(cost))

try:
    usage = {
        "input_tokens": token_total("inputTokens"),
        "cached_input_tokens": token_total("cacheReadTokens", "cachedInputTokens"),
        "cache_write_input_tokens": token_total("cacheCreationTokens", default=0),
        "output_tokens": token_total("outputTokens"),
        "reasoning_output_tokens": token_total("reasoningOutputTokens"),
        "total_tokens": token_total("totalTokens"),
    }
except ValueError:
    sys.exit(1)

json.dump(
    {
        "agent": "codex",
        "session_id": exact_session_id,
        "session_file": root_session_file,
        "total_cost_usd": math.fsum(costs),
        "usage": usage,
    },
    sys.stdout,
    indent=2,
)
print()
' "$session_file" "$exact_session_id" "$sessions_dir"
    )"; then
      ccusage_output=""
      echo "codex adapter: usage unavailable for session $exact_session_id" >&2
    fi
  else
    echo "codex adapter: usage unavailable: npx was not found" >&2
  fi

  if [[ -n "$ccusage_output" ]]; then
    printf '%s' "$ccusage_output" > "$usage_file"
    write_rc=$?
    return "$write_rc"
  fi

  python3 - <<'PY' "$usage_file" "$exact_session_id" "$session_file"
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
  local activity_log="${SPECULA_ACTIVITY_LOG:-/dev/null}"
  local session_id_file=""
  local adapter_dir
  local specula_src
  adapter_dir="$(cd -P "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
  specula_src="$adapter_dir/../../../src"
  if [[ -z "$RESUME_STATE" ]]; then
    if ! session_id_file="$(mktemp "${TMPDIR:-/tmp}/specula-codex-session-XXXXXX.id")"; then
      session_id_file=""
      echo "codex adapter: usage unavailable: unable to create session ID file" >&2
    fi
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
  local -a pipeline_status
  local -a stream_args=(codex "$activity_log" "$log_file")
  local stream_rc
  if [[ -n "$RESUME_STATE" ]]; then
    stream_args+=("$RESUME_STATE" "$RESUME_CWD" "$MODEL" "$EFFORT")
  elif [[ -n "$session_id_file" ]]; then
    stream_args+=("$session_id_file")
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
  set -e

  if (( codex_rc == TRANSIENT_FAILURE_RC )) && [[ "$transient_classified" != true ]]; then
    # Native 74 is EX_IOERR; only a classified provider diagnostic may expose
    # Specula's retry/resume contract to the phase runner.
    codex_rc=1
  fi

  local exact_session_id=""
  if [[ -n "$session_id_file" ]]; then
    IFS= read -r exact_session_id < "$session_id_file" || true
    rm -f "$session_id_file" || true
  fi

  local usage_rc=0
  write_usage_file "$log_file" "$exact_session_id" || usage_rc=$?
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
