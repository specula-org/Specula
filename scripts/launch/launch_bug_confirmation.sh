#!/usr/bin/env bash
#
# Batch launcher: spawn one Claude Code agent per target system for bug confirmation.
# Each agent consolidates MC bugs + code review findings, then attempts to reproduce
# each bug following the bug-confirmation skill methodology.
#
# Usage:
#   bash scripts/launch/launch_bug_confirmation.sh [options] "name" [...]
#
# Example:
#   bash scripts/launch/launch_bug_confirmation.sh hashicorp-raft nuraft
#
# Options:
#   --dry-run           Print commands without executing
#   --check             Only verify prerequisites exist
#   --max-parallel=N    Max concurrent agents (default: 1)
#   --max-turns=N       Max agent turns (default: 0 = unlimited)
#   --agent=NAME        Agent adapter to use (default: claude-code)
#   --claude-alias=NAME Claude CLI profile (default: claude)
#   --artifact=PATH     Explicit path to the artifact repo (overrides auto-detection)
#
# Prerequisites:
#   - Bug report at <name>/spec/bug-report.md (from Phase 3)
#   - Modeling brief at <name>/modeling-brief.md (from Phase 1)
#   - Source repo at <name>/artifact/<repo>/ (or supplied via --artifact)

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SPECULA_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
MAX_PARALLEL=1
MAX_TURNS=0
DRY_RUN=false
CHECK_ONLY=false
AGENT="claude-code"
CLAUDE_ALIAS="${CLAUDE_ALIAS:-claude}"
ARTIFACT=""
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
    --artifact=*) ARTIFACT="${arg#*=}" ;;
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
# Find artifact repo directory
# ──────────────────────────────────────────────────────────
find_repo_dir() {
  local name="$1"
  if [[ -n "$ARTIFACT" ]]; then
    echo "$ARTIFACT"
    return
  fi
  local artifact_dir="$PWD/${name}/artifact"
  if [[ -d "$artifact_dir" ]]; then
    for d in "$artifact_dir"/*/; do
      if [[ -d "${d}.git" || -f "${d}.git" ]]; then
        echo "$d"
        return
      fi
    done
  fi
  if (( ${#TARGETS[@]} == 1 )); then
    echo "$PWD"
    return
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
    local repo_dir
    repo_dir="$(find_repo_dir "$name")"

    printf "  %-20s" "$name"

    if [[ -f "${work_dir}/spec/bug-report.md" ]]; then
      printf "bug-report OK"
    else
      printf "bug-report MISSING"
      ok=false
    fi

    if [[ -f "${work_dir}/modeling-brief.md" ]]; then
      printf "  brief OK"
    else
      printf "  brief MISSING"
      ok=false
    fi

    if [[ -n "$repo_dir" ]]; then
      printf "  repo OK"
    else
      printf "  repo MISSING"
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
  local name="$1" repo_dir="$2"
  local work_dir
  work_dir="$(get_work_dir "$name")"
  local spec_dir="${work_dir}/spec"

  cat <<PROMPT_EOF
# Bug Confirmation Task: ${name}

You are confirming and reproducing bugs found in **${name}** by both model checking and code review.

## Inputs

- **Bug report (MC findings)**: ${spec_dir}/bug-report.md
- **Modeling brief (code review findings)**: ${work_dir}/modeling-brief.md
- **Source code**: ${repo_dir}
- **Spec directory**: ${spec_dir}

## Methodology

Read and follow the **bug-confirmation** skill:
  ${SPECULA_ROOT}/.claude/skills/bug-confirmation/guide.md

## Task

### Step 1: Consolidate all findings

Read both \`bug-report.md\` (MC-confirmed bugs) and \`modeling-brief.md\` (code review findings).
Create a unified list of all bugs/findings, noting for each:
- Source: MC (with counterexample) or code review
- Severity assessment
- Affected code location

Treat every finding as a candidate. Do not pre-filter for "defensive coding", "style", or "theoretical-only" — every candidate goes through Phase 1 investigation and Phase 2 reproduction before classification.

### Step 2: Confirm each bug via investigation

For each finding, follow the bug-confirmation skill Phase 1:
1. Locate and read the relevant code in the source repo
2. Trace the call chain — is the buggy path reachable?
3. Check for existing safeguards that prevent the bug
4. Construct a concrete trigger scenario
5. Investigate developer intent (issue tracker, commits, comments, tests)
6. For findings citing a precedent: re-verify the precedent's prerequisites at this site

Classify each finding as:
- **CONFIRMED**: Code audit confirms the bug is real and reachable
- **FALSE POSITIVE**: Safeguards exist that prevent the bug in practice, or developer intent dismisses it
- **NEEDS REPRODUCTION**: Bug is plausible; reproduction will decide

### Step 3: Mandatory reproduction attempt for every bug

**Every bug must attempt reproduction** — new, known, or historical. Walk the skill's escalation ladder strictly in order (Level 0 black-box → Level 1 timing → Level 2 state injection → Level 3 minimal code modification). Do not stop at Level 0 failure.

Two valid final reproduction statuses:
- **REPRODUCED** — bug triggered; include level reached, the exact command, the copy-paste output, and which line demonstrates the bug
- **REPRODUCTION FAILED** — escalation ladder exhausted; document per-level what was attempted and why it didn't trigger, and state whether you still believe the bug stands on code audit alone

For each bug:
1. Write a self-contained reproduction test to \`${work_dir}/repro/test_bug<N>_*.{py,js,rs,go,c,sh}\`
2. The test MUST use the system's public interfaces at Level 0; escalate only if Level 0 truly failed
3. The test MUST actually be executed, and the output recorded
4. For concurrency bugs: real multi-thread/multi-process scenarios. Sleeps / failpoints to widen race windows are allowed and considered Level 1
5. For distributed systems: use Docker or the system's test framework to set up a real cluster
6. Success criterion: observable anomalous behavior (crash, deadlock, data inconsistency, invariant violation)
7. For known/historical bugs with an upstream reproduction: re-use or adapt it; cite the upstream reproduction; still execute and record output

**Output requirement**: One executable file in \`${work_dir}/repro/\` for EVERY bug — REPRODUCED entries get the working test; REPRODUCTION FAILED entries get the four-level attempt file with per-level comments. The \`confirmed-bugs.md\` entry must include actual test output (copy-paste).

### Step 4: Write final report

Write the final consolidated report to: ${spec_dir}/confirmed-bugs.md

Format:
\`\`\`markdown
# Confirmed Bug Report — ${name}

## Summary
- Total findings reviewed: N
- Reproduced: N
- Reproduction failed (escalation exhausted, claim stands on audit): N
- False positives: N
- Inconclusive: N

## Bug 1: <title>
- **Source**: MC / Code Review
- **Status**: REPRODUCED / REPRODUCTION FAILED / FALSE POSITIVE / NEEDS MORE INFO
- **Severity**: Critical / High / Medium / Low
- **Location**: file:line
- **Description**: ...
- **Trigger scenario**: concrete sequence of events
- **Developer intent investigation**: what was found in issue tracker, commits, comments, tests; or "no developer commentary found"
- **Reproduction test**: repro/test_bug1_xxx.{py,c,...} — escalation level reached (0/1/2/3)
- **Reproduction result**: PASS (bug triggered, paste output) / FAIL (per-level: what was tried, what happened, why it didn't trigger)
- **Recommendation**: ...
\`\`\`

## Critical Rules

1. Follow the bug-confirmation skill strictly — especially the prohibited approaches in Phase 2.
2. **Every bug MUST attempt reproduction and have a test file in repro/.** "Code audit only" is NOT a permitted status. REPRODUCTION FAILED (escalation ladder exhausted, documented per-level) IS a valid final status — it does not invalidate the finding.
3. Walk the escalation ladder strictly in order (Level 0 → 1 → 2 → 3). Do not stop at Level 0 failure; escalate with a documented reason.
4. MC-confirmed bugs with counterexamples are high-confidence; focus reproduction effort there first.
5. Do NOT lower reproduction standards to claim success. If you cannot reproduce after exhausting the ladder, say REPRODUCTION FAILED honestly — but you MUST try all four levels.
6. For each false positive, explain clearly what safeguard prevents the bug, or what developer-intent evidence dismisses it.
7. Actually RUN the reproduction tests and record the output. Do not just write tests without executing them.
PROMPT_EOF

  # Inject per-target extra prompt if present (prefer the target work dir)
  local extra="${work_dir}/.prompt-extra.md"
  if [[ ! -f "$extra" ]]; then
    extra="$PWD/.prompt-extra.md"
  fi
  if [[ -f "$extra" ]]; then
    echo ""
    echo "## Target-Specific Instructions"
    echo ""
    cat "$extra"
  fi
}

# ──────────────────────────────────────────────────────────
# Launch a single Claude Code agent
# ──────────────────────────────────────────────────────────
launch_agent() {
  local name="$1" prompt="$2"
  local work_dir
  work_dir="$(get_work_dir "$name")"
  local log_file="${work_dir}/bug-confirmation.log"
  local prompt_file="${work_dir}/.bug-confirmation-prompt.md"

  echo "$prompt" > "$prompt_file"

  echo "[$(date '+%H:%M:%S')] Launching agent: ${name}"

  if $DRY_RUN; then
    echo "  [DRY RUN] $ADAPTER --prompt=<prompt> --max-turns=${MAX_TURNS} --log=${log_file} --background"
    echo "  Prompt saved: ${prompt_file}"
    return 0
  fi

  "$ADAPTER" --prompt-file="$prompt_file" --max-turns="$MAX_TURNS" --claude-alias="$CLAUDE_ALIAS" --effort=max --log="$log_file" --background &
  local pid=$!
  echo "$pid" > "${work_dir}/bug-confirmation.pid"
  echo "  PID=$pid  Log: $log_file"
}

# ──────────────────────────────────────────────────────────
# Main
# ──────────────────────────────────────────────────────────
main() {
  echo "========================================"
  echo " Specula — Bug Confirmation Batch Runner"
  echo "========================================"
  echo "Targets:      ${#TARGETS[@]}"
  echo "Max parallel: $MAX_PARALLEL"
  echo "Max turns:    $MAX_TURNS"
  echo ""

  echo "Checking prerequisites..."
  if ! check_prereqs; then
    echo ""
    echo "ERROR: Missing prerequisites. Run full pipeline first."
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

    local repo_dir
    repo_dir="$(find_repo_dir "$name")"

    local prompt
    prompt="$(generate_prompt "$name" "$repo_dir")"

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
      running_pids+=("$(cat "$(get_work_dir "$name")/bug-confirmation.pid")")
    fi
    echo ""
  done

  if ! $DRY_RUN; then
    echo "[$(date '+%H:%M:%S')] All agents launched. Waiting..."
    echo "  Monitor: tail -f */bug-confirmation.log"
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
    local report="${work_dir}/spec/confirmed-bugs.md"

    local repro_dir="${work_dir}/repro"
    local repro_count=0
    [[ -d "$repro_dir" ]] && repro_count=$(find "$repro_dir" -name "test_bug*" -type f 2>/dev/null | wc -l)

    if [[ -s "$report" ]]; then
      echo "  ${name}: confirmed-bugs.md written ($(wc -l < "$report") lines, repro/ tests: ${repro_count})"
    elif [[ -f "$report" ]]; then
      echo "  ${name}: confirmed-bugs.md empty (check log; repro/ tests: ${repro_count})"
    else
      echo "  ${name}: (no report — check log; repro/ tests: ${repro_count})"
    fi
  done
}

main
