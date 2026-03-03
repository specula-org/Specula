# TLA+ Verification Workflow (Orchestration)

Iteratively refine a TLA+ spec by alternating between trace validation and model checking until both pass. This ensures the spec faithfully models the system — covering all real behaviors while excluding illegal states.

## Why Iteration is Necessary

- **Trace validation** ensures: spec covers all observed system behaviors (spec ⊇ system)
- **Model checking** ensures: spec doesn't allow illegal states (spec ⊆ legal states)

These pull in opposite directions. Fixing trace failures may loosen the spec (introducing illegal states). Fixing invariant violations may tighten the spec (breaking trace validation). Convergence happens when both pass simultaneously.

## Input

| Item | Description |
|------|-------------|
| Base spec | `base.tla` + `base.cfg` — core specification |
| Trace spec | `Trace.tla` + `Trace.cfg` — trace replay wrapper |
| MC spec | `MC.tla` + `MC.cfg` — model checking wrapper (invariants defined here) |
| Trace files | `.ndjson` files from instrumented test runs |
| Instrumentation spec | `instrumentation-spec.md` — maps spec actions to source code locations |
| Run command | Command to launch TLC for model checking |

## Output

- Verified spec: all traces pass AND no invariant violations

### Required Artifacts

All artifacts are relative to the case study root (e.g., `case-studies/<name>/`):

| Artifact | Path | Description |
|----------|------|-------------|
| Changelog | `spec/changelog.md` | Unified record of all modifications across iterations (format below) |
| MC output | `spec/output/` | TLC model checking output files (counterexamples, statistics) |

---

## Phase 0: Initialization

1. **Verify all files exist**: base spec, trace spec, MC spec, trace files, instrumentation-spec
2. **Read `instrumentation-spec.md`**: understand the mapping between spec actions and source code locations — you'll need this when analyzing failures and making fixes
3. **Create `spec/changelog.md`** (or open existing one)

---

## Phase 1: Trace Validation Round

**Goal**: Ensure all traces pass validation.

**Delegate to sub-skill**: Follow the methodology in `../tla-trace-workflow/guide.md`.

**Steps**:
1. Run `run_trace_validation_parallel` on all trace files
2. For each failing trace: debug and fix following the trace workflow
3. After each fix, re-run `run_trace_validation_parallel` to check for regressions
4. Record each fix in `changelog.md` (see format below)
5. Continue until all traces pass

**When all traces pass**: proceed to Phase 2.

---

## Phase 2: Model Checking Round

**Goal**: Ensure no invariant violations in the spec's state space.

**Delegate to sub-skill**: Follow the methodology in `../tla-checking-workflow/guide.md`.

**Steps**:
1. Launch TLC model checking with the MC spec
2. Monitor for violations
3. For each violation: analyze counterexample, classify (Case A/B/C), and fix following the checking workflow
4. Record each fix in `changelog.md`
5. After fixing, restart model checking to verify fix and find more violations
6. Continue until model checking completes with no violations

**When model checking passes**: proceed to Phase 3.

---

## Phase 3: Convergence Check

**Decision logic**:

- If Phase 2 **modified the spec** → go back to Phase 1 (spec changes may break trace validation)
- If Phase 2 **did not modify the spec** (only invariant changes or no changes) → **done**
- If Phase 1 **modified the spec** in a new round → Phase 2 must re-run after

**Tracking regressions**: If a trace that passed in a previous round now fails, mark it as `[regression]` in changelog. This is informational — handle it the same way as any other failure.

**Termination**: Both phases pass in the same round with no spec modifications needed.

---

## changelog.md Format

Maintain a single `spec/changelog.md`. One line per fix, grouped by round.

```markdown
## Round N - Trace Validation
- [fix] ActionName: brief description of what was wrong and how it was fixed (Trace: filename.ndjson)
- [regression] ActionName: brief description (Trace: filename.ndjson, was passing in Round M)

## Round N - Model Checking
- [fix-inv] InvariantName: brief description of invariant change (Case A)
- [fix-spec] ActionName: brief description of spec change (Case B)
- [bug] ActionName: brief description of real bug found (Case C)

## Result
Converged in N rounds. / Found real bug — stopped.
```

**Keep entries concise** — a few sentences per fix is enough.

---

## Critical Rules

1. **Always start with trace validation.** Ensure spec covers real behavior first, then tighten.
2. **Complete each phase fully before switching.** Don't interleave — finish all traces, then finish model checking.
3. **Delegate to sub-skills.** This layer decides WHAT to run; sub-skills decide HOW to debug and fix.
4. **Record every fix in changelog.** This is the single source of truth for the iteration history.
5. **Autonomous by default.** Apply fixes directly. Only pause for user confirmation if the prompt explicitly requests human-in-the-loop.
6. **Read instrumentation-spec before fixing.** Always know the code location mapping when analyzing failures.

---

## Sub-Skills

- **`../tla-trace-workflow/guide.md`** — Trace validation: validate, debug, fix
- **`../tla-checking-workflow/guide.md`** — Model checking: run, analyze counterexamples, fix

## Related Skills

- **spec-generation** — Produces the TLA+ specs that this workflow verifies
- **code-analysis** — Analyzes system implementation to produce modeling briefs
