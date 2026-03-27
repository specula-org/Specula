# Specula Workflow: Finding Bugs in System Implementations

## What This Is

Specula is a workflow for finding bugs in distributed system and concurrent data structure implementations using TLA+ formal verification. It combines code analysis, TLA+ modeling, trace validation, and bug reproduction into a systematic pipeline.

The core idea: the most critical bugs — protocol safety violations, data loss, deadlocks — have extremely tricky trigger paths. Manual code review can suspect they exist, but cannot prove it. TLA+ model checking can explore the full state space and either confirm the bug with a concrete counterexample or provide confidence that it doesn't exist.

## The Five Phases

```
Phase 1           Phase 2              Phase 2.5            Phase 3                    Phase 4
Code Analysis ──> Spec Generation ──> Harness Generation ──> Validation & Hunting ──> Bug Confirmation
      │                │                    │                      │                       │
 modeling-brief   base.tla, MC.tla     traces/*.ndjson        bug-report.md         confirmed-bugs.md
 (handoff)        Trace.tla            harness/run.sh         spec/output/          repro/test_bug*
```

Each phase has a dedicated skill. The pipeline can be run automatically via `scripts/launch/launch_pipeline.sh` or phase-by-phase interactively.

## System Categories

Specula handles two categories of systems with different trace strategies:

| | Category A: Distributed Systems | Category B: Concurrent/Lock-Free |
|---|---|---|
| Examples | CometBFT, braft, MongoDB, hashicorp-raft | DPDK rte_ring, arc-swap, libomp, papaya |
| Operation timescale | ms (network I/O, disk) | ns (CAS, atomic ops, spin) |
| Trace approach | Single NDJSON file, mutex writer | Per-thread files, rdtsc timebox intervals |
| TLC search | Linear (cursor `l`) | Partial order (`ViablePIDs`) |

See `harness-generation` skill's `guide.md` Step 0 for classification.

---

## Phase 1: Code Analysis

**Skill**: `skills/code_analysis/`

**Goal**: Find bug-prone areas and produce a Modeling Brief that guides spec generation.

### What Happens

1. **Reconnaissance** — Map the codebase: core modules, concurrency model, atomicity boundaries.
2. **Bug Archaeology** — Mine git history and issue tracker for historical bugs. Group into **Bug Families** by shared mechanism.
3. **Deep Analysis** — Systematic code reading guided by Bug Families. Look for: code path inconsistencies, non-atomic persistence with crash windows, missing guards, deviations from the reference algorithm.
4. **Modeling Brief** — Synthesize findings into a concise handoff document. For each Bug Family: mechanism, evidence, modeling approach, invariants.

### Key Principle

Bug Families are the organizing concept. Group by mechanism ("non-atomic persistence with crash window", "missing migrationId filter"), not by file or component. Each Bug Family directly maps to a spec extension.

### Output

- `modeling-brief.md` — Handoff to Phase 2
- `analysis-report.md` — Full audit trail

---

## Phase 2: Spec Generation

**Skill**: `skills/spec_generation/`

**Goal**: Translate the Modeling Brief into a TLA+ specification suite.

### What Happens

1. **Base Spec** (`base.tla`) — Core TLA+ specification. Scope driven by Bug Families, logic faithful to implementation code. Every logic block annotated with `file:line`.
2. **MC Spec** (`MC.tla` + `MC.cfg` + `MC_hunt_*.cfg`) — Counter-bounded fault injection for model checking. Hunting configs target specific bug families.
3. **Trace Spec** (`Trace.tla` + `Trace.cfg`) — Drives TLC through recorded traces to verify spec-implementation consistency.
4. **Instrumentation Spec** (`instrumentation-spec.md`) — Maps spec actions to code locations for harness generation.

### Key Principles

- **Bug-Family driven scope**: Every extension traces to a Bug Family
- **Code-faithful logic**: Model the implementation, not the paper
- **Source line annotations**: Every condition cites `file:line`
- **Split actions where code paths diverge**

---

## Phase 2.5: Harness Generation

**Skill**: `skills/harness-generation/`

**Goal**: Instrument the real system to emit NDJSON traces, write test scenarios, collect traces.

### Output

| File | Purpose |
|------|---------|
| `harness/src/` | Trace module + test scenarios |
| `harness/run.sh` | One-command: build, run tests, collect traces |
| `traces/*.ndjson` | Recorded execution traces |
| `harness/INSTRUMENTATION.md` | Guide for adjusting instrumentation |

For MongoDB case studies: log parsing approach (no C++ recompilation needed). See `case-studies/mongodb-shared-harness.md`.

---

## Phase 3: Validation & Bug Hunting

**Skill**: `skills/validation-workflow/` (orchestration), `skills/tla-trace-workflow/` (trace), `skills/tla-checking-workflow/` (MC)

### 3A: Trace Validation

Verify spec reproduces every state transition in real traces. Catches spec-implementation inconsistencies before hunting.

### 3B: Model Checking — Convergence

Run `MC.cfg` (0 faults) to verify structural invariants hold. Fix spec issues (Case A: invariant too strong, Case B: spec modeling issue).

### 3C: Bug Hunting

Run `MC_hunt_*.cfg` with fault injection. BFS + Simulation strategy:
1. BFS first (30 min) — exhaustive within reachable diameter
2. If diameter ≤ 25 → follow up with simulation (30 min) for deeper states
3. Violation = **Case C** (real bug) — analyze counterexample, cross-reference with code

### Output

- `spec/bug-report.md` — All findings with counterexamples
- `spec/changelog.md` — Spec modifications during validation
- `spec/output/` — TLC output files

---

## Phase 4: Bug Confirmation

**Skill**: `skills/bug-confirmation/`

**Goal**: Confirm MC-found bugs are real and reproduce them.

### Three Sub-Phases

1. **Code Audit** — Trace call chain, check safeguards, construct trigger scenario
2. **Developer Intent** — Search issue tracker, read commit messages, check existing tests
3. **Reproduction (MANDATORY for new bugs)** — Write and execute reproduction test

### Key Rules

- **New bugs MUST have reproduction tests** in `repro/test_bug<N>_*.py`
- Known/historical bugs (matching existing JIRA) don't require reproduction
- "Code audit only" is NOT acceptable for new bugs
- Tests must be actually executed, results recorded

### Output

- `spec/confirmed-bugs.md` — Final report with reproduction results
- `repro/test_bug*` — Executable reproduction tests

---

## Pipeline Automation

### Full Pipeline

```bash
bash scripts/launch/launch_pipeline.sh "system-name|github/repo|Lang|Reference description"
```

Options: `--skip-analysis`, `--skip-specgen`, `--skip-harness`, `--skip-validation`, `--max-parallel=N`

### Scheduler (with quota monitoring)

```bash
bash scripts/exp/scheduler.sh --workers 3 --threshold 80 --queue tasks.queue
```

Pauses when API usage exceeds threshold, waits for reset, resumes automatically.

---

## Directory Structure (per case study)

```
case-studies/<system-name>/
├── analysis-report.md           # Phase 1
├── modeling-brief.md            # Phase 1 → Phase 2 handoff
├── .prompt-extra.md             # Target-specific instructions for pipeline agents
├── artifact/                    # Source code (cloned repo)
│   └── <repo>/
├── spec/
│   ├── base.tla + base.cfg     # Phase 2
│   ├── MC.tla + MC.cfg         # Phase 2
│   ├── MC_hunt_*.cfg           # Phase 2 (per bug family)
│   ├── Trace.tla + Trace.cfg   # Phase 2
│   ├── instrumentation-spec.md # Phase 2
│   ├── bug-report.md           # Phase 3
│   ├── confirmed-bugs.md       # Phase 4
│   ├── changelog.md            # Phase 3
│   └── output/                 # TLC output files
├── harness/
│   ├── src/                    # Trace module + test scenarios
│   ├── run.sh                  # Build + run + collect traces
│   └── INSTRUMENTATION.md      # Adjustment guide
├── traces/                     # NDJSON trace files
│   └── *.ndjson
└── repro/                      # Bug reproduction tests
    └── test_bug*.py
```

---

## Available Skills

| Skill | Phase | Location |
|-------|-------|----------|
| `code_analysis` | 1 | `skills/code_analysis/` |
| `spec_generation` | 2 | `skills/spec_generation/` |
| `harness-generation` | 2.5 | `skills/harness-generation/` |
| `validation-workflow` | 3 (orchestration) | `skills/validation-workflow/` |
| `tla-trace-workflow` | 3A | `skills/tla-trace-workflow/` |
| `tla-checking-workflow` | 3B | `skills/tla-checking-workflow/` |
| `bug-confirmation` | 4 | `skills/bug-confirmation/` |
| `bug_recording` | Any | `skills/bug_recording/` |

## MCP Tools

| Tool | Purpose |
|------|---------|
| `run_trace_validation` | Quick trace-spec consistency check |
| `run_trace_debugging` | Breakpoint-based debugging with hit statistics |
| `run_trace_validation_parallel` | Batch validation of multiple traces |
| `validate_spec_syntax` | Quick TLA+ syntax check |
| `get_tlc_summary` | TLC model checking result overview |
| `get_tlc_state` | Inspect specific states in error trace |
| `compare_tlc_states` | Diff states or track variable changes |
| `run_trace_replay` | Replay trace with custom ALIAS |
| `run_vav_analysis` | Variable assignment validation |
