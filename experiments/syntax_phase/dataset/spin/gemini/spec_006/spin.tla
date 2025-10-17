---- MODULE spin ----
EXTENDS Integers, TLC

CONSTANT Procs

VARIABLES lock_state, pc

vars == <<lock_state, pc>>

\* The set of states a process can be in.
\* - "idle": The process is not attempting to acquire the lock.
\* - "locking": The process is in the busy-wait loop of the lock() method.
\* - "try_locking": The process is attempting a single non-blocking try_lock().
\* - "in_cs": The process holds the lock (is in the critical section).
States == {"idle", "locking", "try_locking", "in_cs"}

TypeOK ==
    /\ lock_state \in BOOLEAN
    /\ pc \in [Procs -> States]

Init ==
    /\ lock_state = FALSE
    /\ pc = [p \in Procs |-> "idle"]

\* A process p decides to call the blocking lock() method.
\* This corresponds to entering the spin loop.
WantToLock(p) ==
    /\ pc[p] = "idle"
    /\ pc' = [pc EXCEPT ![p] = "locking"]
    /\ UNCHANGED lock_state

\* A process p, while spinning, attempts to acquire the lock.
\* This models one iteration of the busy-wait loop containing the atomic
\* compare_exchange(false, true, Acquire, Relaxed).
\* If the lock is free (FALSE), it is acquired and the process enters the CS.
\* If the lock is taken (TRUE), the process remains in the "locking" state,
\* modeling the spin.
AcquireAttempt(p) ==
    /\ pc[p] = "locking"
    /\ \/ /\ lock_state = FALSE
          /\ lock_state' = TRUE
          /\ pc' = [pc EXCEPT ![p] = "in_cs"]
       \/ /\ lock_state = TRUE
          /\ pc' = pc
          /\ UNCHANGED lock_state

\* A process p decides to call the non-blocking try_lock() method.
WantToTryLock(p) ==
    /\ pc[p] = "idle"
    /\ pc' = [pc EXCEPT ![p] = "try_locking"]
    /\ UNCHANGED lock_state

\* A process p attempts the single atomic compare_exchange of try_lock().
\* If the lock is free (FALSE), it is acquired and the process enters the CS.
\* If the lock is taken (TRUE), the attempt fails and the process returns to "idle".
TryLockAttempt(p) ==
    /\ pc[p] = "try_locking"
    /\ \/ /\ lock_state = FALSE
          /\ lock_state' = TRUE
          /\ pc' = [pc EXCEPT ![p] = "in_cs"]
       \/ /\ lock_state = TRUE
          /\ pc' = [pc EXCEPT ![p] = "idle"]
          /\ UNCHANGED lock_state

\* A process p, holding the lock, releases it.
\* This models the Drop implementation of SpinLockGuard, which calls
\* release_lock() and performs a store(false, Release).
ReleaseLock(p) ==
    /\ pc[p] = "in_cs"
    /\ lock_state' = FALSE
    /\ pc' = [pc EXCEPT ![p] = "idle"]

Next ==
    \E p \in Procs:
        \/ WantToLock(p)
        \/ AcquireAttempt(p)
        \/ WantToTryLock(p)
        \/ TryLockAttempt(p)
        \/ ReleaseLock(p)

Spec == Init /\ [][Next]_vars

\* The safety property: at most one process can be in the critical section.
MutualExclusion ==
    Cardinality({p \in Procs : pc[p] = "in_cs"}) <= 1

\* The lock state variable should be TRUE if and only if a process is in the CS.
LockStateConsistent ==
    lock_state = (Cardinality({p \in Procs : pc[p] = "in_cs"}) = 1)

\* Fairness condition to ensure progress.
\* - Every process holding the lock must eventually release it.
\* - Every process trying to acquire the lock must eventually get a chance to attempt it.
Fairness ==
    /\ \A p \in Procs : WF_vars(ReleaseLock(p))
    /\ \A p \in Procs : WF_vars(AcquireAttempt(p))

\* Liveness property: any process that starts spinning will eventually acquire the lock.
Liveness ==
    \A p \in Procs : [](pc[p] = "locking") ~> (pc[p] = "in_cs")

=============================================================================