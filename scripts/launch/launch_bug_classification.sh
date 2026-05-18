#!/usr/bin/env bash
#
# Batch launcher: spawn one Claude Code agent per target system for Phase 4b
# severity classification. Each agent reads the confirmed-bugs.md produced by
# Phase 4a (bug-confirmation) and writes a separate bug-severity.md table
# assigning Critical / High / Medium / Low per bug. No new analysis, no repro
# work, no modification to confirmed-bugs.md.
#
# Usage:
#   bash scripts/launch/launch_bug_classification.sh [options] "name" [...]
#
# Example:
#   bash scripts/launch/launch_bug_classification.sh libgomp_3 autobahn_3
#
# Options:
#   --dry-run           Print commands without executing
#   --check             Only verify prerequisites exist
#   --max-parallel=N    Max concurrent agents (default: 1)
#   --max-turns=N       Max agent turns (default: 0 = unlimited)
#   --agent=NAME        Agent adapter to use (default: claude-code)
#   --claude-alias=NAME Claude CLI profile (default: claude)
#
# Prerequisites:
#   - Confirmed bug report at <name>/spec/confirmed-bugs.md (from Phase 4a)

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SPECULA_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
MAX_PARALLEL=1
MAX_TURNS=0
DRY_RUN=false
CHECK_ONLY=false
AGENT="claude-code"
CLAUDE_ALIAS="${CLAUDE_ALIAS:-claude}"
TARGETS=()

# ──────────────────────────────────────────────────────────
# Parse arguments
# ──────────────────────────────────────────────────────────
for arg in "$@"; do
  case "$arg" in
    --dry-run) DRY_RUN=true ;;
    --check) CHECK_ONLY=true ;;
    --max-parallel=*) MAX_PARALLEL="${arg#*=}" ;;
    --max-turns=*) MAX_TURNS="${arg#*=}" ;;
    --agent=*) AGENT="${arg#*=}" ;;
    --claude-alias=*) CLAUDE_ALIAS="${arg#*=}" ;;
    --help|-h)
      sed -n '2,/^$/{ s/^# //; s/^#//; p }' "$0"
      exit 0
      ;;
    -*) echo "Unknown option: $arg"; exit 1 ;;
    *) TARGETS+=("$arg") ;;
  esac
done

if [[ ${#TARGETS[@]} -eq 0 ]]; then
  TARGETS+=("$(basename "$PWD")")
fi

ADAPTER="$SCRIPT_DIR/adapters/${AGENT}.sh"
if [[ ! -f "$ADAPTER" ]]; then
  echo "ERROR: Unknown agent '${AGENT}' — adapter not found at ${ADAPTER}"
  exit 1
fi

# ──────────────────────────────────────────────────────────
# Resolve working directory for a target
# ──────────────────────────────────────────────────────────
get_work_dir() {
  local name="$1"
  if (( ${#TARGETS[@]} == 1 )); then
    echo "$PWD/.specula-output"
  else
    echo "$PWD/${name}/.specula-output"
  fi
}

# ──────────────────────────────────────────────────────────
# Check prerequisites
# ──────────────────────────────────────────────────────────
check_prereqs() {
  local ok=true
  for name in "${TARGETS[@]}"; do
    name="$(echo "$name" | xargs)"
    local work_dir
    work_dir="$(get_work_dir "$name")"

    printf "  %-20s" "$name"

    if [[ -s "${work_dir}/spec/confirmed-bugs.md" ]]; then
      printf "confirmed-bugs OK"
    else
      printf "confirmed-bugs MISSING"
      ok=false
    fi

    echo ""
  done
  $ok
}

# ──────────────────────────────────────────────────────────
# Generate agent prompt
# ──────────────────────────────────────────────────────────
generate_prompt() {
  local name="$1"
  local work_dir
  work_dir="$(get_work_dir "$name")"
  local spec_dir="${work_dir}/spec"

  cat <<PROMPT_EOF
# Bug Classification Task: ${name}

You are assigning a Severity tier to each bug in **${name}**'s already-confirmed bug report.

## Input

- **Confirmed bug report (from Phase 4a)**: ${spec_dir}/confirmed-bugs.md

## Output

- **Severity classification**: ${spec_dir}/bug-severity.md (you create this file)

## Methodology

Read and follow the **bug-classification** skill:
  ${SPECULA_ROOT}/.claude/skills/bug-classification/guide.md

The skill defines the four-tier Severity rubric, the per-bug output schema, the single-responsibility constraint (do not modify confirmed-bugs.md), and the rule that Severity is independent of reproduction status (a REPRODUCTION FAILED Critical bug is still Critical).

## Task

1. Read every entry in \`confirmed-bugs.md\` end-to-end.
2. For each \`## Bug N:\` header, identify the worst observable consequence the bug enables under realistic conditions (reachable code path + within the system's stated fault / threat model).
3. Map to the rubric (Critical / High / Medium / Low; \`—\` only for FALSE POSITIVE).
4. Write one row per bug to \`${spec_dir}/bug-severity.md\` using the schema in the skill's "Output schema" section. Include the mandatory Summary block at the top.

## Constraints

- **Do not modify \`confirmed-bugs.md\`.** It is read-only input. The classifier's only write is \`bug-severity.md\`.
- **Do not change \`Status\` fields** (REPRODUCED / REPRODUCTION FAILED / FALSE POSITIVE / NEEDS MORE INFO). Phase 4a is authoritative on Status; you are authoritative only on Severity.
- **Do not lower Severity because reproduction failed or was hard.** A bug's worst-case impact does not depend on how easy it was to trigger in a sandbox. Use the bug's audit + trigger-scenario + developer-intent evidence to judge severity, not the Reproduction result.
- **Do not add bugs** that are not already in \`confirmed-bugs.md\`. The classifier is not the place to introduce new findings.
- **Do not write Phase 4a-style content** (no code audit, no reproduction script, no investigation). One row per bug, 1–2 sentences of Reasoning each.
- One row per \`## Bug N:\` header. Numbering must match the input (do not renumber if there are gaps).
- Every Severity must be one of \`Critical\`, \`High\`, \`Medium\`, \`Low\`, or \`—\` (use \`—\` only for FALSE POSITIVE).

## Output format

\`\`\`markdown
# Severity Classification — ${name}

## Summary

- Total bugs: N
- Critical: N
- High: N
- Medium: N
- Low: N
- FALSE POSITIVE (no severity): N

## Per-bug classification

| Bug | Title | Status | Severity | Reasoning |
|-----|-------|--------|----------|-----------|
| 1   | <title from ## Bug 1:>  | REPRODUCED         | High     | <1-2 sentences: consequence + reachability> |
| 2   | <title from ## Bug 2:>  | REPRODUCTION FAILED | Critical | <consequence + why FAILED doesn't lower severity> |
| 3   | <title from ## Bug 3:>  | FALSE POSITIVE     | —        | <1 sentence acknowledging FP call is sound>     |
\`\`\`

When done, verify against the skill's "Output validation checklist" (one row per Bug header in the input, every Severity in {Critical, High, Medium, Low, —}, every — row has Status = FALSE POSITIVE, every non-— Reasoning names at least one consequence and one trigger surface, Summary counts add up).
PROMPT_EOF
}

# ──────────────────────────────────────────────────────────
# Launch a single Claude Code agent
# ──────────────────────────────────────────────────────────
launch_agent() {
  local name="$1" prompt="$2"
  local work_dir
  work_dir="$(get_work_dir "$name")"
  local log_file="${work_dir}/bug-classification.log"
  local prompt_file="${work_dir}/.bug-classification-prompt.md"

  echo "$prompt" > "$prompt_file"

  echo "[$(date '+%H:%M:%S')] Launching agent: ${name}"

  if $DRY_RUN; then
    echo "  [DRY RUN] $ADAPTER --prompt-file=<prompt> --max-turns=${MAX_TURNS} --log=${log_file} --background"
    echo "  Prompt saved: ${prompt_file}"
    return 0
  fi

  "$ADAPTER" --prompt-file="$prompt_file" --max-turns="$MAX_TURNS" --claude-alias="$CLAUDE_ALIAS" --effort=max --log="$log_file" --background &
  local pid=$!
  echo "$pid" > "${work_dir}/bug-classification.pid"
  echo "  PID=$pid  Log: $log_file"
}

# ──────────────────────────────────────────────────────────
# Main
# ──────────────────────────────────────────────────────────
main() {
  echo "========================================"
  echo " Specula — Bug Classification Batch Runner"
  echo "========================================"
  echo "Targets:      ${#TARGETS[@]}"
  echo "Max parallel: $MAX_PARALLEL"
  echo "Max turns:    $MAX_TURNS"
  echo ""

  echo "Checking prerequisites..."
  if ! check_prereqs; then
    echo ""
    echo "ERROR: Missing prerequisites. Run Phase 4a (launch_bug_confirmation.sh) first."
    exit 1
  fi
  echo ""

  if $CHECK_ONLY; then
    echo "All prerequisites OK."
    exit 0
  fi

  local running_pids=()

  for name in "${TARGETS[@]}"; do
    name="$(echo "$name" | xargs)"

    local prompt
    prompt="$(generate_prompt "$name")"

    # Throttle
    while (( ${#running_pids[@]} >= MAX_PARALLEL )); do
      local new_pids=()
      for pid in "${running_pids[@]}"; do
        if kill -0 "$pid" 2>/dev/null; then
          new_pids+=("$pid")
        fi
      done
      running_pids=("${new_pids[@]}")
      if (( ${#running_pids[@]} >= MAX_PARALLEL )); then
        sleep 5
      fi
    done

    launch_agent "$name" "$prompt"
    if ! $DRY_RUN; then
      running_pids+=("$(cat "$(get_work_dir "$name")/bug-classification.pid")")
    fi
    echo ""
  done

  if ! $DRY_RUN; then
    echo "[$(date '+%H:%M:%S')] All agents launched. Waiting..."
    echo "  Monitor: tail -f */bug-classification.log"
    echo ""
    wait
    echo "[$(date '+%H:%M:%S')] All agents completed."
  fi

  # Summary
  echo ""
  echo "========================================"
  echo " Results"
  echo "========================================"
  for name in "${TARGETS[@]}"; do
    name="$(echo "$name" | xargs)"
    local work_dir
    work_dir="$(get_work_dir "$name")"
    local report="${work_dir}/spec/bug-severity.md"

    if [[ -s "$report" ]]; then
      # Pull the Summary counts if present
      local total=$(grep -E "^- Total bugs:" "$report" 2>/dev/null | head -1 | grep -oE "[0-9]+" | head -1)
      local critical=$(grep -E "^- Critical:" "$report" 2>/dev/null | head -1 | grep -oE "[0-9]+" | head -1)
      local high=$(grep -E "^- High:" "$report" 2>/dev/null | head -1 | grep -oE "[0-9]+" | head -1)
      local medium=$(grep -E "^- Medium:" "$report" 2>/dev/null | head -1 | grep -oE "[0-9]+" | head -1)
      local low=$(grep -E "^- Low:" "$report" 2>/dev/null | head -1 | grep -oE "[0-9]+" | head -1)
      local fp=$(grep -E "^- FALSE POSITIVE" "$report" 2>/dev/null | head -1 | grep -oE "[0-9]+" | head -1)
      echo "  ${name}: total=${total:-?}  C=${critical:-?} H=${high:-?} M=${medium:-?} L=${low:-?} FP=${fp:-?}"
    elif [[ -f "$report" ]]; then
      echo "  ${name}: bug-severity.md empty (check log)"
    else
      echo "  ${name}: (no report — check log)"
    fi
  done
}

main
