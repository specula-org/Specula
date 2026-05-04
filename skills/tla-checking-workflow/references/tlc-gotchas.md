# TLC Gotchas

Quick reference for non-obvious TLC behaviors that produce silent false positives or confusing failures. If TLC gives a result that doesn't match what you expected, scan this list before debugging the spec.

## `-deadlock` flag DISABLES deadlock checking

Counterintuitive: the `-deadlock` flag turns deadlock detection **off**, not on. Deadlock checking is enabled by default.

| Want to check for deadlocks? | Want to suppress deadlock errors? |
|---|---|
| Don't pass `-deadlock`. (Default behavior.) | Pass `-deadlock`. |

Common case: trace validation specs use `-deadlock` because trace exhaustion is detected via the `TraceMatched` temporal property, not via deadlock. Model-checking specs almost always want deadlock checking ON, so omit the flag.

## Simulation mode does not check deadlocks

`-simulate` (random-walk mode) cannot detect deadlocks. If you need to check for deadlock states, use BFS (omit `-simulate`). Simulation is only valid for invariant violations and temporal properties along the sampled path.

If your bug hunting depends on deadlock detection, configure a BFS run, not simulation.

## `~>` (leads-to) trivially passes without fairness

A temporal property like `A ~> B` requires fairness annotations on the actions that should make it eventually hold. Without `WF_vars(Action)` or `SF_vars(Action)`, TLC can stutter forever in a state where `A` is true but `B` never becomes true, and the property formally holds because of the stuttering loophole.

Symptom: TLC reports the temporal property holds, but you suspect it shouldn't.

Fix: add the appropriate fairness constraint to the spec (typically in the `Spec` definition: `Spec == Init /\ [][Next]_vars /\ WF_vars(Action1) /\ ...`). Also requires BFS, not simulation.

## `SYMMETRY` in cfg must reference a named operator

This fails:

```
SYMMETRY Permutations(Server)
```

This works:

```
\* in MC.tla
ModelSymmetry == Permutations(Server)
```

```
\* in MC.cfg
SYMMETRY ModelSymmetry
```

The cfg parser only accepts a single identifier as the symmetry operand. Inline expressions silently fail or report a parse error depending on TLC version.

## Action substitution in cfg requires matching arity

```
\* in MC.cfg
ScheduleTask <- MCScheduleTask
```

This works only if both actions have the same number of arguments. If `MCScheduleTask` adds parameters (e.g., a counter to fault-bound it), substitution fails with an arity mismatch.

Workaround: don't use action substitution. Define a separate `MCNext` and `MCSpec` in the MC module:

```
MCNext == MCScheduleTask(...) \/ ... \/ Next
MCSpec == Init /\ [][MCNext]_vars
```

Then `SPECIFICATION MCSpec` in the cfg.

## TLA+ string comparison with `<` `>` is unreliable

String values in TLA+ are atoms; lexicographic comparison via `<` or `>` does not work portably. Sorting `"s1" > "s2"` may give different results than expected, and TLC may not even reject the expression.

Fix: define an explicit integer ordering and compare integers.

```
ServerOrder == [s1 |-> 1, s2 |-> 2, s3 |-> 3]
\* compare ServerOrder[s1] < ServerOrder[s2]  instead of  s1 < s2
```

## `Trace.cfg` without `PROPERTIES TraceMatched` reports false-positive success

A trace validation cfg that omits `PROPERTIES TraceMatched` will report "no errors" even if the trace cursor never advances — TLC has nothing to check, so it trivially succeeds.

Fix: in `Trace.tla` define `TraceMatched == <>(l > Len(TraceLog))`, and in `Trace.cfg` include `PROPERTIES TraceMatched`. Without this, validation success is meaningless.

(See also `tla-trace-workflow/references/validation.md` for the full trace validation prerequisites.)

## Unconstrained silent actions cause infinite branching

Trace specs use silent actions to handle implementation state changes that don't emit trace events. If a silent action has no precondition, TLC will fire it at every state and never terminate — appearing as "TLC hangs" or "depth grows without bound".

Fix: every silent action must have a tight precondition that limits when it fires (e.g., bound by a counter, gate on the next-event type, gate on a specific state condition). If you can't articulate the precondition, the action probably shouldn't be a silent action.

(See also `spec_generation/references/trace-spec-pattern.md` for silent-action design.)

## Heap exhaustion vs off-heap exhaustion

`-m` controls Java heap; `-M` controls off-heap (used by `OffHeapDiskFPSet`). Symptoms differ:

- **`OutOfMemoryError: Java heap space`** — increase `-m`, not `-M`.
- **`Cannot allocate native memory` / process killed by OOM killer** — off-heap or system memory pressure; reduce `-M` or free system RAM.
- **GC overhead warnings, slowdowns** — heap is undersized for the working set; increase `-m` or reduce state space.

Rule of thumb on a dedicated machine: `-m` = 25-30% of system RAM, `-M` = 50-60% of system RAM, leaving ~15% for OS and Java overhead.

## Symptom → likely cause

| Symptom | First thing to check |
|---|---|
| TLC reports success but you expected a violation | `~>` property without fairness, or `Trace.cfg` without `PROPERTIES TraceMatched` |
| TLC hangs / depth grows without bound | Unconstrained silent action |
| TLC errors with arity mismatch on `<-` | cfg action substitution; switch to `SPECIFICATION MCSpec` |
| TLC parses but no symmetry reduction observed | `SYMMETRY` references inline expression instead of named operator |
| Comparisons between server identifiers behave wrong | TLA+ string `<` / `>` — use integer mapping |
| No deadlock detected when one should exist | `-deadlock` flag was passed (it disables detection), or running in `-simulate` mode |
| `OutOfMemoryError` mid-run | Distinguish heap (`-m`) vs off-heap (`-M`) before increasing |
