# TLA+ Model Checking Workflow

Run TLC model checking, monitor execution, analyze counterexamples, and determine whether violations stem from overly-strong invariants, spec modeling issues, or real system bugs.

## Input / Output

**Input**: Model checking spec (`MC.tla` + `MC.cfg`), system implementation source code (ground truth), run command

**Output**: Verified spec (no violations) or classified counterexamples

**By default, execute autonomously.** Only pause for user confirmation if the prompt explicitly requests human-in-the-loop.

---

## Core Concepts (MUST REMEMBER)

### Implementation is Ground Truth

The system implementation is the single source of truth for determining:
- Whether a behavior is **possible** in the real system
- Whether the spec **correctly models** the implementation
- Whether an invariant violation represents a **real bug**

You MUST cross-reference counterexamples against implementation code before making any judgment.

### Three Counterexample Classifications

Every counterexample falls into exactly one category:

| Case | Meaning | Who is Wrong | Action |
|------|---------|-------------|--------|
| **Case A** | Invariant Too Strong | Invariant | Weaken the invariant |
| **Case B** | Spec Modeling Issue | Spec | Fix the spec to match implementation |
| **Case C** | Real Bug | Implementation | STOP — report to user immediately |

### Autonomous by Default

Apply fixes directly without waiting for user confirmation. If the prompt explicitly requests human-in-the-loop, pause before each modification for approval.

---

## Phase 1: Start Model Checking

**Goal**: Launch TLC and confirm it is running correctly.

**Steps**:

1. Navigate to the working directory specified by the user
2. Execute the run command provided by the user. Typical form:
   ```bash
   /path/to/start_background.sh -s MCSpec.tla -c MCSpec.cfg [options]
   ```
3. Verify the process started by checking the log file (typically `nohup.out`). **Save all TLC output files to `spec/output/`** — rename from `nohup.out` to a descriptive name (e.g., `output/MC_run1.out`, `output/MC_ve_bfs.out`).
4. Confirm TLC is initializing (look for spec parsing, constant initialization, state space exploration starting)

### Runtime Parameters

These parameters apply to **all** model checking runs — convergence and bug hunting alike. The run duration is the primary constraint; do not constrain state space size.

| Parameter | Rule | Notes |
|-----------|------|-------|
| **Timeout** | **30 minutes** per run (`-t 30`) | The single hard constraint. If TLC hasn't found a violation in 30 min, the run ends. |
| **Workers** | Match the machine (`-w auto` or explicit core count) | Detect available CPUs and use all of them. |
| **Heap memory** | Match the machine (e.g., `-m 50G`) | Use most of available RAM. Leave headroom for OS and off-heap. |
| **Off-heap memory** | Match the machine (e.g., `-M 200G`) | For `OffHeapDiskFPSet`. Set to available physical memory minus heap. |
| **Simulation depth** | 50–100 (`-p 50` to `-p 100`) | Shorter (50) for simple protocols (few actions, shallow state graphs). Longer (100) for complex protocols (many interleaving actions, deep state graphs). |
| **Simulation traces** | As many as possible (`-n 999999999`) | Let the timeout be the stopping condition, not trace count. |
| **State space size** | **Do not constrain.** | Let TLC explore as much as possible within the 30-min window. |

**Common run script options**:
| Flag | Purpose | Example |
|------|---------|---------|
| `-s` | Spec file | `-s MCetcdraft.tla` |
| `-c` | Config file | `-c MCetcdraft.cfg` |
| `-S` | Simulation mode | `-S` |
| `-n` | Number of simulation traces | `-n 999999999` |
| `-p` | Simulation depth | `-p 100` |
| `-m` | Heap memory | `-m 50G` |
| `-M` | Off-heap memory | `-M 200G` |
| `-w` | Worker threads | `-w auto` |
| `-t` | Timeout (minutes) | `-t 30` |
| `-j` | JSON trace dump file | `-j counterexample.json` |
| `-D` | Enable deadlock checking | `-D` |
| `-C` | Continue after errors | `-C` |

---

## Phase 2: Monitor Running Status

**Goal**: Track progress and detect violations early.

**Method**: Periodically (every 30-60 seconds) read the tail of the log file.

**What to look for**:
- **Progress**: Number of states generated/explored, queue depth
- **Violations**: Lines containing `Error:`, `Invariant`, `violated`, `Counterexample`
- **Completion**: `Model checking completed` or similar
- **Resource issues**: `OutOfMemoryError`, `GC overhead`, timeout messages

**When a violation is found**: Proceed to Phase 3.

**When model checking completes with no violations**: Report success to user. No further action needed.

---

## Phase 3: Counterexample Analysis (Core Task)

**Goal**: Analyze counterexample traces, classify each violation, and propose fixes.

### Step 1: Read the Counterexample

Use the MCP tools to understand the violation:

1. **`get_tlc_summary`** — Get an overview: which invariant was violated, trace length, action sequence, statistics
2. **`get_tlc_state`** — Inspect specific states. Start with the last state (where the violation occurs), then work backwards
3. **`compare_tlc_states`** — Compare consecutive states to understand what changed, or track a variable across the entire trace

Typical analysis sequence:
```
get_tlc_summary          → understand what was violated and the overall trace shape
get_tlc_state (last)     → see the violating state
compare_tlc_states       → diff last two states to see what transition triggered the violation
get_tlc_state (range)    → read the full trace for context
```

### Step 2: Understand the Violated Property

Read the invariant definition in the spec. Understand exactly what condition was violated and why the final state fails to satisfy it.

### Step 3: Cross-Reference with Implementation (CRITICAL)

This is the most important step. Read the relevant implementation source code to determine:
- Can this sequence of events actually happen in the real system?
- Does the spec correctly model the implementation's behavior?
- Is the invariant capturing a genuine safety requirement?

If the counterexample's preconditions look implausible in the real system (e.g., the violation requires a state combination you suspect the implementation prevents), run the procedure in `references/spec-fidelity-checklist.md` before classifying. The most common false positive is a Case C that's actually a Case B — the spec under-models a guard the implementation has.

### Step 4: Classify the Counterexample

#### Case A: Invariant Too Strong

**Signs**:
- The behavior in the counterexample is reasonable and expected in the real system
- The implementation intentionally allows this state
- The invariant is too restrictive — it excludes legitimate system states

**Action**:
1. Explain to the user why the behavior is reasonable (cite implementation code)
2. Propose a weakened invariant that permits this legitimate behavior
3. Apply the modification
4. Restart model checking

#### Case B: Spec Modeling Issue

**Signs**:
- The counterexample shows behavior that cannot happen in the real system
- The spec allows state transitions that the implementation prevents
- There is a gap between the spec's model and the implementation

**Action**:
1. Identify the problematic Action or state transition in the spec
2. Show the corresponding implementation code as evidence
3. Propose a spec modification that correctly models the implementation
4. Apply the modification
5. Restart model checking

#### Case C: Real Bug Found

**Signs**:
- The counterexample shows a realistically possible execution sequence
- The spec accurately reflects the implementation
- The invariant correctly captures a safety requirement
- Yet the system can reach a state that violates the invariant

**Action** (depends on context):

*During spec validation (convergence):*
1. Describe the execution path in detail, state by state
2. Show confirming implementation code that proves this path is possible
3. Analyze impact and severity
4. Record as `[bug]` in `changelog.md`, save TLC output to `spec/output/`
5. **Continue convergence** — do not stop the validation loop

*During bug hunting (post-convergence):*
1. Describe the execution path in detail, state by state
2. Show confirming implementation code that proves this path is possible
3. Analyze impact and severity
4. Record in `spec/bug-report.md` with full details (counterexample summary, root cause, affected code)

**Case C is the most valuable outcome** — prioritize its discovery.

### Advanced Analysis with Trace Replay

When the standard tools don't provide enough detail, use `run_trace_replay` to re-execute the trace with custom ALIAS operators:

1. Define an ALIAS operator in the spec to expose computed expressions:
   ```tla
   DebugAlias == [
     currentTerm |-> currentTerm,
     state |-> state,
     quorum |-> {Q \in SUBSET Server : IsQuorum(Q)}
   ]
   ```
2. Add `ALIAS DebugAlias` to the config file
3. Run `run_trace_replay` to generate a JSON trace with the extra information
4. Analyze the replayed trace with `get_tlc_summary` / `get_tlc_state` / `compare_tlc_states`

---

## Critical Rules

1. **Implementation is ground truth.** Never judge a counterexample without reading the relevant implementation code.
2. **Classify before fixing.** Determine Case A / B / C before proposing any change.
3. **Autonomous by default.** Apply fixes directly unless the prompt requests human-in-the-loop.
4. **Prioritize Case C.** Real bug discovery is the most valuable outcome of model checking.
5. **Document everything.** Record every counterexample analysis and modification.
6. **Use tools systematically.** Start with `get_tlc_summary` for overview, then drill into states. Don't guess from raw log text when structured tools are available.
7. **Restart after fixes.** After modifying spec or invariants, restart model checking from Phase 1 to verify the fix and continue checking.

---

## Available Tools

| Tool | Purpose | When to Use |
|------|---------|-------------|
| `get_tlc_summary` | Overview of TLC results: violation, trace length, actions | First step after finding a violation |
| `get_tlc_state` | Inspect specific states by index, range, or nested path | Drill into the counterexample trace |
| `compare_tlc_states` | Diff two states or track a variable across the trace | Understand what changed between states |
| `run_trace_replay` | Re-execute trace with ALIAS for extra computed values | When standard tools don't provide enough detail |
| `run_vav_analysis` | Variable Assignment Validation on spec | Check that all actions assign all variables in every branch |

## Reference: Tool Usage Patterns

### get_tlc_summary
```json
{"file_path": "nohup.out"}
```
Returns: `violation_name`, `trace_length`, `actions`, `action_frequency`, `statistics`, `variables`

### get_tlc_state
```json
{"file_path": "nohup.out", "index": -1}
{"file_path": "nohup.out", "indices": "-3:"}
{"file_path": "nohup.out", "index": "last", "path": "currentTerm.s1"}
{"file_path": "nohup.out", "index": 5, "variables": ["currentTerm", "state"]}
```

### compare_tlc_states
```json
{"file_path": "nohup.out", "index1": -2, "index2": -1}
{"file_path": "nohup.out", "track_variable": "currentTerm"}
{"file_path": "nohup.out", "track_variable": "state", "track_path": "s1"}
```

### run_trace_replay
```json
{
  "spec_file": "MCetcdraft.tla",
  "trace_file": "counterexample.json",
  "work_dir": "/path/to/spec",
  "config_file": "MCetcdraft.cfg",
  "trace_format": "json"
}
```

---

## Related Skills

- **tla-trace-workflow** — Validates implementation traces against TLA+ specs (complementary to model checking)
- **spec-generation** — Produces the TLA+ specs that this workflow checks
- **code-analysis** — Analyzes system implementation to produce modeling briefs

## Additional References

For additional examples beyond the built-in ones, see the [Specula case-studies repository](https://github.com/specula-org/specula-case-studies) which contains 60+ completed case studies across distributed systems, consensus protocols, and concurrent data structures.
