---- MODULE spin ----
EXTENDS Integers, TLC

CONSTANTS ProcSet
ASSUME ProcSet = {"p1", "p2"}

VARIABLES lock_state, pc

vars == <<lock_state, pc>>

TypeOK ==
    /\ lock_state \in BOOLEAN
    /\ pc \in [ProcSet -> {"idle", "locking", "try_locking", "critical"}]

Init ==
    /\ lock_state = FALSE
    /\ pc = [p \in ProcSet |-> "idle"]

\* A process decides to call the blocking lock() method.
RequestLock(self) ==
    /\ pc[self] = "idle"
    /\ pc' = [pc EXCEPT ![self] = "locking"]
    /\ UNCHANGED lock_state

\* A process decides to call the non-blocking try_lock() method.
RequestTryLock(self) ==
    /\ pc[self] = "idle"
    /\ pc' = [pc EXCEPT ![self] = "try_locking"]
    /\ UNCHANGED lock_state

\* A process attempts the compare-and-exchange and succeeds.
\* This applies to both lock() and try_lock() attempts.
Acquire(self) ==
    /\ pc[self] \in {"locking", "try_locking"}
    /\ lock_state = FALSE
    /\ lock_state' = TRUE
    /\ pc' = [pc EXCEPT ![self] = "critical"]

\* A process in the lock() method fails the compare-and-exchange
\* and continues to spin (busy-wait).
Spin(self) ==
    /\ pc[self] = "locking"
    /\ lock_state = TRUE
    /\ UNCHANGED vars

\* A process in the try_lock() method fails the compare-and-exchange
\* and gives up, returning to idle.
FailTryLock(self) ==
    /\ pc[self] = "try_locking"
    /\ lock_state = TRUE
    /\ pc' = [pc EXCEPT ![self] = "idle"]
    /\ UNCHANGED lock_state

\* A process holding the lock releases it (modeling the guard's Drop).
Release(self) ==
    /\ pc[self] = "critical"
    /\ lock_state' = FALSE
    /\ pc' = [pc EXCEPT ![self] = "idle"]

Next ==
    \E self \in ProcSet:
        \/ RequestLock(self)
        \/ RequestTryLock(self)
        \/ Acquire(self)
        \/ Spin(self)
        \/ FailTryLock(self)
        \/ Release(self)

Spec == Init /\ [][Next]_vars

\* Fairness ensures that no process is stuck forever if it can make progress.
Fairness == \A self \in ProcSet: WF_self(Next)

\* Safety Property: At most one process can be in the critical section.
MutualExclusion ==
    Cardinality({p \in ProcSet : pc[p] = "critical"}) <= 1

THEOREM Spec => []MutualExclusion

\* Liveness Property: If a process tries to lock, it will eventually succeed,
\* assuming fairness.
Liveness ==
    \A self \in ProcSet:
        (pc[self] = "locking") ~> (pc[self] = "critical")

THEOREM Spec /\ Fairness => Liveness

====