# TLA+ Verification Workflow (Orchestration)

Iteratively refine a TLA+ spec by alternating between trace validation and model checking until both pass, then hunt for real bugs using the converged spec. This ensures the spec faithfully models the system — covering all real behaviors while excluding illegal states — and then uses the trusted spec to find implementation bugs.

## Why Iteration is Necessary

- **Trace validation** ensures: spec covers all observed system behaviors (spec ⊇ system)
- **Model checking** ensures: spec doesn't allow illegal states (spec ⊆ legal states)

These pull in opposite directions. Fixing trace failures may loosen the spec (introducing illegal states). Fixing invariant violations may tighten the spec (breaking trace validation). Convergence happens when both pass simultaneously.

## Input

| Item | Description |
|------|-------------|
| Base spec | `base.tla` + `base.cfg` — core specification |
| Trace spec | `Trace.tla` + `Trace.cfg` — trace replay wrapper |
| MC spec | `MC.tla` + `MC.cfg` — model checking wrapper (standard + structural invariants) |
| Hunting configs | `MC_hunt_*.cfg` / `MC_family*.cfg` — bug-family-specific configs (for bug hunting) |
| Trace files | `.ndjson` files from instrumented test runs |
| Instrumentation spec | `instrumentation-spec.md` — maps spec actions to source code locations |
| Run command | Command to launch TLC for model checking |

## Output

- Verified spec: all traces pass AND no invariant violations

### Required Artifacts

All artifacts are relative to `.specula-output/`:

| Artifact | Path | Description |
|----------|------|-------------|
| Changelog | `spec/changelog.md` | Unified record of all modifications across iterations (format below) |
| MC output | `spec/output/` | TLC model checking output files (counterexamples, statistics) |
| Bug report | `spec/bug-report.md` | Bug hunting results — produced after convergence (even if no bugs found) |

---

## Phase 0: Initialization

1. **Verify all files exist**: base spec, trace spec, MC spec, trace files, instrumentation-spec, hunting configs
2. **Read `instrumentation-spec.md`**: understand the mapping between spec actions and source code locations — you'll need this when analyzing failures and making fixes
3. **Read `harness/INSTRUMENTATION.md`**: understand how to adjust instrumentation if trace validation reveals capture timing or field issues
4. **Check `Trace.cfg` has `PROPERTIES TraceMatched`** (uncommented). If missing, add it — without it validation reports false positives.
5. **Create `spec/changelog.md`** (or open existing one)

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

**Config**: Use **`MC.cfg` only** — standard safety + structural invariants. Do NOT use hunting configs (`MC_hunt_*.cfg`) in this phase; those are for bug hunting after convergence.

**Run duration**: 30 minutes per run. See `../tla-checking-workflow/guide.md` Phase 1 "Runtime Parameters" for worker, memory, and simulation depth settings.

**Delegate to sub-skill**: Follow the methodology in `../tla-checking-workflow/guide.md`.

**Steps**:
1. Launch TLC model checking with `MC.cfg`
2. Monitor for violations
3. For each violation: analyze counterexample, classify (Case A/B/C), and fix following the checking workflow
4. Record each fix in `changelog.md`
5. **Case C (real bug)**: record as `[bug]` in changelog, save TLC output to `spec/output/`, then **continue** model checking — do not stop convergence
6. After fixing Case A/B, restart model checking to verify fix and find more violations
7. Continue until model checking completes with no violations

**When model checking passes**: proceed to Phase 3.

---

## Phase 3: Convergence Check

**Decision logic**:

- If Phase 2 **modified the spec** → go back to Phase 1 (spec changes may break trace validation)
- If Phase 2 **did not modify the spec** (only invariant changes or no changes) → **converged**, proceed to Bug Hunting
- If Phase 1 **modified the spec** in a new round → Phase 2 must re-run after

**Tracking regressions**: If a trace that passed in a previous round now fails, mark it as `[regression]` in changelog. This is informational — handle it the same way as any other failure.

**Convergence**: Both phases pass in the same round with no spec modifications needed. The spec is now trusted. Proceed to Bug Hunting.

---

## Bug Hunting

**Precondition**: Spec has converged (Phase 3 passed). The spec is trusted to faithfully model the implementation.

**Goal**: Use the converged spec to find real implementation bugs via targeted model checking with bug-family configs.

### BFS + Simulation Strategy

For each hunting config, alternate between BFS and simulation to maximize coverage:

1. **BFS first** (30 min) — exhaustive within reachable diameter. Check the diameter achieved in TLC output.
2. **If diameter ≤ 25** — the BFS run is too shallow to expose many bugs. Follow up with a **simulation run** (30 min) on the same config to reach deeper states.
3. **If diameter > 25** — BFS coverage is likely sufficient. Simulation follow-up is optional.

**Do NOT shrink config bounds to make BFS go deeper.** Counter bounds (timeout limits, crash limits, etc.) directly control which bug scenarios are reachable. Reducing them to fit BFS eliminates the very interleavings where bugs hide. When BFS is too shallow, use simulation for depth — not tighter bounds.

### Steps

1. Collect any `[bug]` entries already recorded in `changelog.md` during Phase 2 (Case C found during convergence) — these will be included in the final report
2. For each `MC_hunt_*.cfg` / `MC_family*.cfg`:
   - **Run 1 (BFS)**: Launch TLC model checking (30 min). Record diameter and state count from output.
   - If violation found → **Case C** (real bug). Analyze counterexample: describe execution path, cross-reference with implementation code, identify root cause and affected code locations.
   - If no violation and diameter ≤ 25 → **Run 2 (Simulation)**: Launch TLC simulation (30 min, `-S -n 999999999`) on the same config for deeper exploration.
   - Save all TLC output to `spec/output/`
3. Produce `spec/bug-report.md` with all findings — **read `references/bug-report-format.md`** for the template
4. If no bugs found across all configs: still write the report (state space coverage, diameter achieved per config, + "no violations found")

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
Converged in N rounds. Bug hunting: M bugs found / no bugs found.
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

- **harness-generation** — Previous phase (2.5): produces harness, traces, and `INSTRUMENTATION.md` for adjusting instrumentation during validation
- **spec-generation** — Produces the TLA+ specs that this workflow verifies
- **code-analysis** — Analyzes system implementation to produce modeling briefs
