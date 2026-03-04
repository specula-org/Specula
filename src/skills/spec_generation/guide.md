# TLA+ Spec Generation

Bug-family driven modeling: each spec extension exists because a Bug Family in the Modeling Brief identified a concrete mechanism that needs verification. The spec logic within each action MUST faithfully follow the implementation's control flow, with every logic block annotated to its source code location.

## Input / Output

**Input**: `modeling-brief.md` + source code access

**Output** (written to files sequentially):

| Phase | Output | Description |
|-------|--------|-------------|
| 1 | `base.tla` + `base.cfg` | Base spec with all extensions |
| 2 | `MC.tla` + `MC.cfg` + `MC_hunt_*.cfg` | Model checking spec + hunting configs per bug family |
| 3 | `Trace.tla` + `Trace.cfg` | Trace validation spec |
| 4 | `instrumentation-spec.md` | Action-to-code mapping for harness generation |

**Single agent, sequential phases.** Each phase writes output to files. If context is compressed mid-session, re-read your own output files to recover.

---

## Phase 1: Base Spec

**Goal**: Write the core TLA+ specification with bug-family driven extensions.

1. **Read the Modeling Brief** — note each Bug Family's mechanism, suggested variables/actions, priority
2. **Read source code (targeted)** — only the functions referenced in the brief, not the entire codebase
3. **Design variables** — standard protocol variables + extension variables motivated by Bug Families
4. **Write actions** — name after implementation functions, follow code's control flow faithfully, annotate every logic block with `file:line`
5. **Write invariants** — standard safety properties + extension invariants targeting Bug Families + structural invariants
6. **Write Init and Next**

**Read `references/base-spec-methodology.md`** for patterns, annotation style, and action design.

---

## Phase 2: MC Spec

**Goal**: Wrap the base spec with counter-bounded actions for exhaustive model checking.

Counter-bound fault-injection actions (timeout, crash, message loss, etc.). Do NOT bound deterministic/reactive actions. Add symmetry reduction, message buffer constraints, structural invariants, and temporal properties.

**Generate two types of config**:
- **`MC.cfg`** — standard safety + structural invariants. Used during spec validation (convergence). Extension invariants (bug-family-specific) should be listed but **commented out**.
- **`MC_hunt_<family>.cfg`** — one per bug family from the modeling brief. Tight bounds (reduce irrelevant actions to 0-1), only the target invariant + core safety invariants. Used during bug hunting after spec converges.

**Read `references/mc-spec-pattern.md`** for the full template and hunting config pattern.

---

## Phase 3: Trace Spec

**Goal**: Replay implementation traces against the base spec to verify consistency.

Key concepts: cursor variable `l` walks through trace events; action wrappers match events, call base actions, validate post-state, advance cursor; silent actions handle impl state changes without trace events (must be tightly constrained).

**Trace file location**: Trace files (`.ndjson`) are stored in `traces/` (sibling to `spec/`). The `JsonFile` operator in `Trace.tla` must default to `../traces/<name>.ndjson`, with an `IOEnv.JSON` override for per-run selection:
```tla
JsonFile ==
    IF "JSON" \in DOMAIN IOEnv THEN IOEnv.JSON
    ELSE "../traces/trace.ndjson"
```

**Read `references/trace-spec-pattern.md`** for the full template and silent action patterns.

---

## Phase 4: Instrumentation Spec

**Goal**: Produce a mapping document (`instrumentation-spec.md`) describing how to instrument the source code to produce traces compatible with the trace spec.

For each spec action, specify: spec action name, code location (`file:line`), trigger point (before/after which operation), and event fields to capture.

**Read `references/instrumentation-spec-format.md`** for the full format.

---

## Critical Rules

1. **Every extension traces to a Bug Family.** No Bug Family reference → don't add the extension.
2. **Model the implementation, not the paper.** Deviations from the reference algorithm are where bugs live.
3. **Follow the code's control flow faithfully.** Do not simplify, reorder, or merge logic that the code keeps separate.
4. **Annotate every logic block with source lines.** Every condition, branch, and state update must cite `file:line`. Not optional.
5. **Write to files early and often.** Insurance against context loss.
6. **Split actions where code paths diverge.** Merging hides bugs.
7. **Name actions after implementation functions.** Enables cross-referencing with code.
8. **Silent actions must be tightly constrained.** Unconstrained silent actions cause state space explosion.
9. **MC spec bounds fault-injection, not normal operations.**

---

## Reference Files

- **`references/base-spec-methodology.md`** — Variable design, action design, annotation style, invariants, helpers
- **`references/mc-spec-pattern.md`** — MC spec template with counter-bounded actions
- **`references/trace-spec-pattern.md`** — Trace spec template with event matching and silent actions
- **`references/instrumentation-spec-format.md`** — Format for the action-to-code mapping document
- **`examples/hashicorp-raft-spec-generation.md`** — Complete worked example

## Related Skills

- **code_analysis** — Previous phase: produces the Modeling Brief
- **harness-generation** — Next phase (2.5): instruments the system and collects traces using `instrumentation-spec.md`
- **validation-workflow** — Phase 3: validates the spec using traces and model checking
