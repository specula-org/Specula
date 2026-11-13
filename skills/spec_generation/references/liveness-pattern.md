# Liveness Pattern

How to check a Liveness property from modeling brief §5. Safety invariants remain the main target. Each liveness property gets its own hunt cfg, and all liveness cfgs together should take no more than about 30% of the bug-hunting time (see `validation-workflow/guide.md`).

## Choose a checkable property

Check a property whose progress follows from the system's own actions eventually running: a handler processing a delivered message, a worker draining its queue, a retry loop resending, a waiter being woken after a signal. Typical shapes:

```tla
RequestServed == \A r \in Request : Pending(r) ~> Done(r)
WaiterWoken   == \A t \in Thread : (Waiting(t) /\ Signaled) ~> Running(t)
```

Do not check properties that only hold with favorable timing or randomization, such as "eventually a leader is elected" when candidates can split the vote forever. The model allows those behaviors, so the property fails without telling you anything about the implementation.

## Add fairness: `LiveSpec`

Without fairness, liveness properties fail by stuttering. Add fairness in `MC.tla` for the actions the implementation guarantees will eventually run, and cite the code that guarantees it:

```tla
Fairness ==
    \* worker.c:120 - the worker loop runs while the queue is non-empty
    /\ \A t \in Thread : WF_mc_vars(MCWorkerStep(t))
    \* node.go:88 - a running node handles every delivered message
    /\ \A s \in Server : WF_mc_vars(MCHandleMessage(s))

LiveSpec == MCSpec /\ Fairness
```

- `WF` when the action stays enabled until it is taken; `SF` when it is enabled repeatedly but can be disabled in between (for example, acquiring a lock that other threads keep taking, when the implementation guarantees the waiter is not starved).
- Quantify over whoever the guarantee is for. `WF_mc_vars(\E s \in Server : A(s))` only guarantees that some server takes `A`; `\A s \in Server : WF_mc_vars(A(s))` guarantees it for each server.
- Never put fairness on fault actions. Fairness without a code citation hides real progress failures.

## Bounds: faults stop, progress does not

- Keep the counters on fault actions (crash, message loss, injected errors). Once they run out, faults stop, and the property asks whether the system makes progress after that.
- Bound the workload (client requests, operations per thread) as usual.
- Do not let actions the property depends on run out. If progress needs a timer, retry, or heartbeat that the MC spec bounds, remove its bound in the liveness model when the state space stays finite without it. Otherwise make the property conditional, for example `Pending(r) ~> (Done(r) \/ retries = MaxRetry)`, and note in the bug report that behaviors which use up the bound are not checked.
- Keep the remaining bounds small enough for BFS to finish within the run's time budget. Shrink constants unrelated to the property first.

## The `_live` cfg

Name it `MC_hunt_<scenario>_live.cfg`, after the Scenario the property targets.

```
SPECIFICATION LiveSpec
CONSTANTS
    Server = {s1, s2}
    MaxCrashLimit = 1
    ...
INVARIANT TypeOK
PROPERTY RequestServed
```

- One `PROPERTY` per cfg. TLC does not report which temporal property failed.
- No `SYMMETRY`, `VIEW`, or `CONSTRAINT`. Each one can hide liveness violations or report ones that do not exist (see `tla-checking-workflow/references/tlc-gotchas.md`).
- Operator overrides (`<-`) work as in the other cfgs. Other invariants are optional; the safety cfgs already check them.

Run `_live` cfgs with BFS and with deadlock checking off; `tla-checking-workflow/guide.md` covers running them and reading their counterexamples.
