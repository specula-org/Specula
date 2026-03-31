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

write_usage_file() {
  local log_file="$1"
  local sessions_dir="${CODEX_HOME:-$HOME/.codex}/sessions"
  local marker_file="$2"
  local usage_file="${log_file%.log}.usage.json"

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
    return 0
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
}

run_codex() {
  local log_file="$1"
  local marker_file
  marker_file="$(mktemp)"

  codex exec \
    --dangerously-bypass-approvals-and-sandbox \
    "$PROMPT" \
    > "$log_file" 2>&1 || true

  write_usage_file "$log_file" "$marker_file"
  rm -f "$marker_file"
}

if $BACKGROUND; then
  nohup bash -lc "$(declare -f write_usage_file run_codex); PROMPT=$(printf '%q' "$PROMPT"); run_codex $(printf '%q' "$LOG_FILE")" >/dev/null 2>&1 &
  echo $!
else
  run_codex "$LOG_FILE"
fi
