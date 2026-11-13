# TLC Gotchas

Quick reference for non-obvious TLC behaviors that produce silent false positives or confusing failures. If TLC gives a result that doesn't match what you expected, scan this list before debugging the spec.

## `-deadlock` flag DISABLES deadlock checking

Counterintuitive: the `-deadlock` flag turns deadlock detection **off**, not on. Deadlock checking is enabled by default.

| Want to check for deadlocks? | Want to suppress deadlock errors? |
|---|---|
| Don't pass `-deadlock`. (Default behavior.) | Pass `-deadlock`. |

Common case: trace validation specs use `-deadlock` because trace exhaustion is detected via the `TraceMatched` temporal property, not via deadlock. Model-checking specs almost always want deadlock checking ON, so omit the flag.

## Simulation mode does not check deadlocks

`-simulate` (random-walk mode) cannot detect deadlocks. If you need to check for deadlock states, use BFS (omit `-simulate`). Simulation is only valid for invariant violations and action properties along the sampled path; it misses most liveness violations (see below).

If your bug hunting depends on deadlock detection, configure a BFS run, not simulation.

## Liveness without fairness fails trivially by stuttering

`Spec == Init /\ [][Next]_vars` allows behaviors that stop taking steps forever. A liveness property such as `A ~> B` or `<>P` is therefore violated as soon as TLC reaches a state where the property is still waiting for something to happen (for `A ~> B`, a state where `A` holds but `B` does not): the behavior can simply stutter there. TLC warns that temporal properties are being verified without a fairness constraint, and the counterexample ends with `State N: Stuttering`.

Symptom: a liveness counterexample that ends in `Stuttering`, usually right after its premise becomes true.

Such a counterexample only shows that the model is allowed to stop; it says nothing about the implementation. Add fairness to the `Spec` used for liveness checking, for the actions the implementation guarantees will eventually run: `WF_vars(A)` when `A` stays enabled until it is taken, `SF_vars(A)` when `A` is enabled repeatedly but not continuously. Each fairness assumption is a claim about the implementation, so cite the code that justifies it; fairness on an action the implementation does not guarantee hides real progress failures. With justified fairness in place, a remaining counterexample either loops (`Back to state N`) or stutters in a state where no fair action is enabled. Run liveness checks in BFS mode.

## `SYMMETRY` makes liveness results unreliable

TLC warns "Declaring symmetry during liveness checking is dangerous. It might cause TLC to miss violations of the stated liveness properties." It can also go the other way: with symmetry, TLC can print a counterexample that does not violate the property at all, while the same cfg without `SYMMETRY` passes. Check liveness properties with a cfg that has no `SYMMETRY`; keep symmetry for invariant-only cfgs.

## Simulation mode misses most liveness violations

`-simulate` reports a liveness violation only when a random trace happens to revisit a state and close a loop. It does not report counterexamples that end in stuttering. Check liveness properties with BFS.

## `CONSTRAINT` removes behaviors from liveness checking

States that fail a `CONSTRAINT` are not explored further. A progress failure that only happens in such states is not reported: the run ends with "No error has been found" and no warning. Bound liveness models with counters in action guards instead.

## `VIEW` can fabricate liveness loops

A `VIEW` merges states that differ only in the variables it leaves out. For safety that is usually harmless, but liveness checking runs on the merged graph. If the view drops fault counters, a bounded fault looks unbounded: TLC can report a loop in which the fault fires forever, although the counter stops it after a few steps. If the view drops a variable the property depends on, TLC can report a violation that does not exist. Check liveness properties with a cfg that has no `VIEW`.

## Bounded progress actions make liveness fail

MC specs often bound every action with a counter (`MaxTimeoutLimit`, `HeartbeatLimit`, `RequestLimit`). Once the counter of an action that is needed for progress runs out, that action is disabled forever; fairness cannot help, and the liveness property fails with a counterexample that ends in `Stuttering`. This says nothing about the implementation. In a liveness model, bound fault actions only, or state the property so that it only requires progress while the bound has not been reached.

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
| TLC reports success but you expected a violation | `Trace.cfg` without `PROPERTIES TraceMatched`; for liveness, `SYMMETRY`, `CONSTRAINT`, or `-simulate` |
| Liveness counterexample ends in `Stuttering` | No fairness for the action that should make progress, or its counter bound ran out |
| Liveness counterexample does not violate the property, or loops through a bounded fault | `SYMMETRY` or `VIEW` in the cfg |
| TLC hangs / depth grows without bound | Unconstrained silent action |
| TLC errors with arity mismatch on `<-` | cfg action substitution; switch to `SPECIFICATION MCSpec` |
| TLC parses but no symmetry reduction observed | `SYMMETRY` references inline expression instead of named operator |
| Comparisons between server identifiers behave wrong | TLA+ string `<` / `>` — use integer mapping |
| No deadlock detected when one should exist | `-deadlock` flag was passed (it disables detection), or running in `-simulate` mode |
| `OutOfMemoryError` mid-run | Distinguish heap (`-m`) vs off-heap (`-M`) before increasing |
