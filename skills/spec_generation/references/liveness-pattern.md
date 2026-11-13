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

Without fairness, liveness properties fail by stuttering. Decide the fairness when you write `LiveSpec`, before any liveness run, from what the implementation's scheduling guarantees.

The default is weak fairness per process or thread on all of its non-fault steps: a running node or thread keeps taking steps while it has one to take. Most implementations guarantee this through an event loop, a worker thread, or the OS scheduler; cite that code.

```tla
\* node.go:210 - a running node's event loop handles every queued message
\* and every fired timer
NodeStep(s) ==
    \/ MCHandleMessage(s)
    \/ MCHandleTimeout(s)
    \/ ...                       \* every non-fault action of s

Fairness == \A s \in Server : WF_mc_vars(NodeStep(s))

LiveSpec == MCSpec /\ Fairness
```

- Quantify over processes or threads. `WF_mc_vars(\E s \in Server : NodeStep(s))` only guarantees that some server takes a step; `\A s \in Server : WF_mc_vars(NodeStep(s))` guarantees it for each server.
- Fairness on a single action, and any `SF`, are stronger claims. Use them only when the code guarantees that specific action (for example, a dedicated timer that always fires, or a lock that hands off in FIFO order so a waiter is not starved), cite it, and keep them few.
- Never put fairness on fault actions.
- Fairness is a claim about the implementation that trace validation cannot check. Never add or strengthen fairness to make a property hold. After a liveness counterexample, change fairness only with a code citation showing that the implementation guarantees the action runs, and log the change as `[fix-fairness]` in `changelog.md`.

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
