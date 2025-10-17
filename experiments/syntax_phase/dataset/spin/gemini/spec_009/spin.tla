---- MODULE spin ----
EXTENDS Integers, TLC

CONSTANT Proc

VARIABLES lock_state, pc

vars == <<lock_state, pc>>

States == {"idle", "req_lock", "req_try_lock", "spinning", "in_cs"}

TypeOK ==
    /\ lock_state \in BOOLEAN
    /\ pc \in [Proc -> States]

Init ==
    /\ lock_state = FALSE
    /\ pc = [p \in Proc |-> "idle"]

\* A process decides to call the blocking lock() method.
RequestLock(p) ==
    /\ pc[p] = "idle"
    /\ pc' = [pc EXCEPT ![p] = "req_lock"]
    /\ UNCHANGED <<lock_state>>

\* A process decides to call the non-blocking try_lock() method.
RequestTryLock(p) ==
    /\ pc[p] = "idle"
    /\ pc' = [pc EXCEPT ![p] = "req_try_lock"]
    /\ UNCHANGED <<lock_state>>

\* Models a successful atomic compare-exchange(false, true).
\* The process acquires the lock and enters the critical section.
AcquireLock(p) ==
    /\ pc[p] \in {"req_lock", "req_try_lock", "spinning"}
    /\ lock_state = FALSE
    /\ lock_state' = TRUE
    /\ pc' = [pc EXCEPT ![p] = "in_cs"]

\* Models a failed compare-exchange within the blocking lock() loop.
\* The process starts or continues to spin.
Spin(p) ==
    /\ pc[p] \in {"req_lock", "spinning"}
    /\ lock_state = TRUE
    /\ pc' = [pc EXCEPT ![p] = "spinning"]
    /\ UNCHANGED <<lock_state>>

\* Models a failed compare-exchange for the non-blocking try_lock().
\* The process gives up and returns to idle.
TryLockFail(p) ==
    /\ pc[p] = "req_try_lock"
    /\ lock_state = TRUE
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ UNCHANGED <<lock_state>>

\* Models the release of the lock when the SpinLockGuard is dropped.
\* The process leaves the critical section.
ReleaseLock(p) ==
    /\ pc[p] = "in_cs"
    /\ lock_state' = FALSE
    /\ pc' = [pc EXCEPT ![p] = "idle"]

\* The set of actions a single process can take.
ProcAction(p) ==
    \/ RequestLock(p)
    \/ RequestTryLock(p)
    \/ AcquireLock(p)
    \/ Spin(p)
    \/ TryLockFail(p)
    \/ ReleaseLock(p)

Next ==
    \E p \in Proc: ProcAction(p)

Spec == Init /\ [][Next]_vars

\* Fairness assumption: No process is starved forever by the scheduler.
\* If a process can take an action, it eventually will.
Fairness == \A p \in Proc: WF_vars(ProcAction(p))

\* Safety property: At most one process can be in the critical section.
MutualExclusion ==
    Cardinality({p \in Proc : pc[p] = "in_cs"}) <= 1

\* Liveness property: A process that requests a blocking lock will eventually
\* acquire it, assuming the lock is eventually released by any holder.
EventualAcquisition ==
    \A p \in Proc:
        (pc[p] \in {"req_lock", "spinning"}) ~> (pc[p] = "in_cs")

=============================================================================