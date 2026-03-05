# TLA+ Trace Validation Workflow

Validate implementation traces against TLA+ specifications. Diagnose and fix validation failures through layered debugging.

## Input / Output

**Input**: Trace spec (`Trace.tla` + `Trace.cfg`) + trace file (`.ndjson`) + base spec

**Output**: Validated spec (trace passes) or corrected spec

**By default, execute autonomously.** Only pause for user confirmation if the prompt explicitly requests human-in-the-loop.

---

## Core Concepts (MUST REMEMBER)

### Variable `l` Semantics

`l = N` means "currently validating TraceLog[N]", NOT "already validated N lines". TraceLog is 1-indexed.

### TLCGet("level") vs `l`

**ALWAYS use `TLCGet("level")` in breakpoint conditions, NOT `l`.** `l` only works in the Trace wrapper spec; `TLCGet("level")` works everywhere including the base spec.

### Breakpoint Hit Semantics

A breakpoint hit means TLC is **attempting** to evaluate that line — it does NOT mean the condition is TRUE. To know if a condition is TRUE, you must inspect variable values.

### Conjunction Short-Circuit Evaluation

TLC evaluates `/\` conditions top to bottom. If a condition is FALSE, subsequent conditions are not evaluated. Decreasing hit counts indicate filtering.

---

## Phase 1: Validation

**Goal**: Determine if trace matches spec.

**Tool**: `run_trace_validation`

**Prerequisite**: Before running validation, check that `Trace.cfg` has `PROPERTIES TraceMatched` (uncommented). If missing, add it. Without this, TLC reports "no errors" even when the trace is never consumed — a false positive.

Three outcomes:
- `success` — trace is valid, done
- `trace_mismatch` — go to Phase 2
- `error` — check syntax with `validate_spec_syntax`

Key fields for `trace_mismatch`: `failed_trace_line` (which trace line failed), `last_state_number` (use for breakpoint condition), `suggestion` (ready-to-use debugging hint).

**Read `references/validation.md`** for detailed guidance.

---

## Phase 2: Debugging

**Goal**: Locate the exact condition that failed.

**Tool**: `run_trace_debugging`

**Methodology: Layered Debugging (Coarse -> Fine)**

1. **Coarse-grained localization**: Set breakpoints at major branches to identify which code path is relevant
2. **Fine-grained localization**: Set breakpoints at each condition in the relevant branch
3. **Variable inspection**: Use `evaluate` or `collect_variables` to understand WHY a condition failed

Key patterns:
- Decreasing hit counts show short-circuit filtering
- First line with 0 hits is where failure occurs
- If last hit is an action call, the action failed internally -> debug inside that action

**Read `references/debugging.md`** for detailed methodology.

---

## Phase 3: Fix

**Goal**: Fix the spec or trace to resolve inconsistency.

**First, classify the error type:**

| Error Type | Description | Action |
|------------|-------------|--------|
| **Inconsistency Error** | Spec is objectively wrong about system behavior | Fix spec, read system code for evidence |
| **Abstraction Gap** | Spec is correct but at different abstraction level | Judge based on modeling goals (see `references/fix.md`) |

For Inconsistency Errors: read system source code -> find evidence -> fix **base spec** (not trace comparison logic) -> verify with `run_trace_validation_parallel`.

For Abstraction Gaps: understand the gap -> judge whether bridging it helps find more bugs or is just cosmetic -> choose fix strategy accordingly.

**Read `references/fix.md`** for detailed workflow.

---

## Phase 4: Cleanup

The user may request not to clean up the generated files. Otherwise, run `clean_traces`.

---

## Critical Rules

1. **Always start with `run_trace_validation`.** It's faster and gives exact failure point.
2. **Use `TLCGet("level")` in all breakpoint conditions**, never `l`.
3. **Debug layer by layer.** Coarse -> fine -> variable inspection. Don't skip layers.
4. **If last hit is an action call, debug INSIDE that action.** The problem is internal.
5. **Classify error type before fixing.** Inconsistency Error vs Abstraction Gap require different strategies.
6. **Fix the base spec, not the trace comparison logic.** Unless there is no other option.
7. **Trace.cfg must have `PROPERTIES TraceMatched`.** Without it, validation silently produces false positives. See Phase 1 prerequisite above.

---

## Available Tools

| Tool | Purpose | When to Use |
|------|---------|-------------|
| `run_trace_validation` | Quick validation check | First step, always |
| `run_trace_debugging` | Set breakpoints, collect statistics | After validation fails |
| `get_trace_info` | Check trace file info | Before validation |
| `validate_spec_syntax` | Check spec syntax | If TLC reports syntax errors |
| `run_trace_validation_parallel` | Check against multiple traces | After proposed fix |
| `clean_traces` | Delete generated files | Final cleanup |

## Reference Files

- **`references/validation.md`** — Validation tool parameters, response types, usage examples
- **`references/debugging.md`** — Layered debugging methodology, hit pattern analysis, variable inspection
- **`references/fix.md`** — Error classification, fix workflow

## Related Skills

- **spec-generation** — Previous phase: produces the TLA+ specs
- **code-analysis** — First phase: produces the Modeling Brief
