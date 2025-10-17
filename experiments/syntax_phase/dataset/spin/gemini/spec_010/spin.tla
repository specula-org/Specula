---- MODULE spin ----
EXTENDS Naturals, TLC

CONSTANTS Proc
ASSUME Proc = { "p1", "p2" }

VARIABLES
    \* The state of the spinlock's AtomicBool.
    \* FALSE means unlocked, TRUE means locked.
    lock_is_held,

    \* The program counter for each process.
    \* "idle": Not attempting to acquire the lock.
    \* "spinning": In the busy-wait loop of the lock() method.
    \* "in_cs": Holds the lock and is in the critical section.
    pc,

    \* A shared resource protected by the spinlock to demonstrate mutual exclusion.
    protected_data

vars == << lock_is_held, pc, protected_data >>

\* The set of possible states for a process.
PCStates == {"idle", "spinning", "in_cs"}

\* Initial state of the system.
Init ==
    /\ lock_is_held = FALSE
    /\ pc = [p \in Proc |-> "idle"]
    /\ protected_data = 0

\* A process p decides to call the lock() method and starts spinning.
\* This corresponds to entering the `while !self.try_acquire_lock()` loop.
CallLock(p) ==
    /\ pc[p] = "idle"
    /\ pc' = [pc EXCEPT ![p] = "spinning"]
    /\ UNCHANGED << lock_is_held, protected_data >>

\* A spinning process p attempts to acquire the lock.
\* This models one iteration of the busy-wait loop, containing the
\* atomic compare_exchange(false, true) operation.
\* If the lock is free (FALSE), it acquires it and enters the critical section.
\* If the lock is taken (TRUE), it remains in the "spinning" state (busy-waits).
AttemptAcquire(p) ==
    /\ pc[p] = "spinning"
    /\ IF lock_is_held = FALSE
       THEN /\ lock_is_held' = TRUE
            /\ pc' = [pc EXCEPT ![p] = "in_cs"]
       ELSE /\ lock_is_held' = TRUE
            /\ pc' = pc
    /\ UNCHANGED protected_data

\* A process p calls try_lock().
\* This is a single, non-blocking attempt to perform compare_exchange(false, true).
\* If the lock is free, it is acquired. If not, the process remains idle.
TryLock(p) ==
    /\ pc[p] = "idle"
    /\ IF lock_is_held = FALSE
       THEN /\ lock_is_held' = TRUE
            /\ pc' = [pc EXCEPT ![p] = "in_cs"]
       ELSE /\ lock_is_held' = TRUE
            /\ pc' = pc
    /\ UNCHANGED protected_data

\* Process p holds the lock and is in the critical section. It finishes its work
\* and releases the lock. This corresponds to the SpinLockGuard going out of scope (Drop),
\* which performs an atomic store(false).
Unlock(p) ==
    /\ pc[p] = "in_cs"
    /\ lock_is_held' = FALSE
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ protected_data' = protected_data + 1

\* The next-state relation for the system.
Next ==
    \E p \in Proc:
        \/ CallLock(p)
        \/ AttemptAcquire(p)
        \/ TryLock(p)
        \/ Unlock(p)

\* The full specification of the system.
Spec == Init /\ [][Next]_vars

\* --- Invariants ---

\* The lock state is consistent with which processes are in the critical section.
LockStateConsistency == lock_is_held <=> (\E p \in Proc: pc[p] = "in_cs")

\* At most one process can be in the critical section at any time.
MutualExclusion ==
    Cardinality({p \in Proc : pc[p] = "in_cs"}) \in {0, 1}

\* The type correctness invariant for model checking.
TypeOK ==
    /\ lock_is_held \in BOOLEAN
    /\ pc \in [Proc -> PCStates]
    /\ protected_data \in Nat
    /\ LockStateConsistency
    /\ MutualExclusion

\* --- Liveness & Fairness ---

\* To prevent starvation, we assume weak fairness for each process's actions
\* that can resolve a waiting state.
\* A spinning process must eventually get to attempt acquisition.
\* A process in the CS must eventually unlock.
Fairness ==
    /\ \A p \in Proc : WF_vars(AttemptAcquire(p))
    /\ \A p \in Proc : WF_vars(Unlock(p))

\* If a process starts spinning, it will eventually acquire the lock (enter the CS).
Liveness ==
    \A p \in Proc : (pc[p] = "spinning") ~> (pc[p] = "in_cs")

====