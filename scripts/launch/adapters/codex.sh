#!/usr/bin/env bash
# Adapter: codex
# Capabilities: max-turns, model-select, effort-select, auto-approve, background, stop-gate
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
#   --help                 Show this help

set -euo pipefail

PROMPT=""
PROMPT_FILE=""
MAX_TURNS=""
LOG_FILE=""
BACKGROUND=false
CLAUDE_ALIAS=""
EFFORT=""
MODEL=""

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
    --help|-h)
      sed -n '2,/^$/{ s/^# //; s/^#//; p }' "$0"
      exit 0
      ;;
    *) echo "codex adapter: unknown option: $arg" >&2; exit 1 ;;
  esac
done

# Flag wins over env; empty (neither set) -> codex config.toml default.
MODEL="${MODEL:-${CODEX_MODEL:-}}"
EFFORT="${EFFORT:-${CODEX_EFFORT:-}}"

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

write_usage_file() {
  local log_file="$1"
  local sessions_dir="${CODEX_HOME:-$HOME/.codex}/sessions"
  local marker_file="$2"
  local usage_file="${log_file%.log}.usage.json"
  local write_rc=0

  python3 - <<'PY' "$usage_file"
import json
import sys

with open(sys.argv[1], "w") as f:
    json.dump(
        {
            "agent": "codex",
            "session_id": None,
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
  session_path="$(
    find "$sessions_dir" -type f -name 'rollout-*.jsonl' -newer "$marker_file" 2>/dev/null \
    | sort \
    | tail -n1
  )"

  [[ -n "$session_path" ]] || return 0

  local session_file
  local session_id
  session_file="$(basename "$session_path" .jsonl)"
  session_id="${session_path#${sessions_dir}/}"
  session_id="${session_id%.jsonl}"

  local ccusage_output=""
  if command -v npx >/dev/null 2>&1; then
    ccusage_output="$(
      npx @ccusage/codex@latest session --json 2>/dev/null \
      | python3 -c '
import json
import sys

session_file = sys.argv[1]

try:
    data = json.load(sys.stdin)
except Exception:
    sys.exit(1)

for session in data.get("sessions", []):
    if session.get("sessionFile") == session_file:
        json.dump(
            {
                "agent": "codex",
                "session_id": session.get("sessionId"),
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
' "$session_file" 2>/dev/null
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
  local marker_file
  local activity_log="${SPECULA_ACTIVITY_LOG:-}"
  local adapter_dir
  adapter_dir="$(cd -P "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
  marker_file="$(mktemp)"

  # ── Optional outer srt sandbox (M1.3) ──
  # Opt-in via SPECULA_SANDBOX=on; additive — off/unset leaves the codex argv
  # byte-for-byte. One outer layer wraps codex and every descendant (TLC/MCP/
  # build); the inner --dangerously-bypass-approvals-and-sandbox stays (YOLO,
  # no nested second sandbox). Backend path repo-relative, overridable.
  local -a cmd=()
  if [[ "${SPECULA_SANDBOX:-}" == "on" ]]; then
    local backend
    backend="${SPECULA_SANDBOX_BACKEND:-$adapter_dir/../sandbox/backend.mjs}"
    cmd+=(node "$backend" --workspace "${SPECULA_WORK_DIR:-$PWD}" --)
  fi
  cmd+=(codex exec --dangerously-bypass-approvals-and-sandbox)
  # Model / reasoning effort (additive — empty leaves codex config.toml default).
  [[ -n "$MODEL" ]] && cmd+=(-m "$MODEL")
  [[ -n "$EFFORT" ]] && cmd+=(-c "model_reasoning_effort=$EFFORT")

  local codex_rc=0
  set +e
  if [[ -n "$activity_log" ]]; then
    local event_helper
    local -a pipeline_status
    local stream_rc
    event_helper="$adapter_dir/../../../src/specula/adapters/event_stream.py"
    "${cmd[@]}" --json "$PROMPT" 2>&1 | python3 "$event_helper" codex "$activity_log" "$log_file"
    pipeline_status=("${PIPESTATUS[@]}")
    codex_rc="${pipeline_status[0]}"
    stream_rc="${pipeline_status[1]}"
    if (( codex_rc == 0 )); then
      codex_rc="$stream_rc"
    fi
  else
    "${cmd[@]}" "$PROMPT" > "$log_file" 2>&1
    codex_rc=$?
  fi
  set -e

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
# SPECULA_WORK_DIR (see src/specula/stop_gate.py). Codex discovers hooks from
# the project layer (<git toplevel of cwd>/.codex/hooks.json), so arm the gate
# by writing a Stop hook there; per-run specifics travel via env, so the file
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
if [[ -n "${SPECULA_PHASE:-}" && -n "${SPECULA_WORK_DIR:-}" \
      && "${SPECULA_STOP_GATE:-on}" != "off" && -d "${SPECULA_WORK_DIR:-}" ]]; then
  ADAPTER_DIR="$(cd -P "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
  GATE_PY="$ADAPTER_DIR/../../../src/specula/stop_gate.py"
  HOOKS_ROOT="$(git rev-parse --show-toplevel 2>/dev/null || pwd)"
  HOOKS_FILE="$HOOKS_ROOT/.codex/hooks.json"
  HOOKS_PREEXISTED=false
  [[ -e "$HOOKS_FILE" ]] && HOOKS_PREEXISTED=true
  {
    python3 "$GATE_PY" reset "$SPECULA_WORK_DIR" &&   # fresh fuse per agent run
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
