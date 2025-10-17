---- MODULE spin ----
EXTENDS Integers, TLC

CONSTANTS Thread
ASSUME Thread \subseteq {"t1", "t2"}

VARIABLE locked, holder, pc

vars == <<locked, holder, pc>>
NoHolder == "NoHolder"

TypeOK ==
    /\ locked \in BOOLEAN
    /\ holder \in Thread \cup {NoHolder}
    /\ pc \in [Thread -> {"idle", "attempt_lock", "attempt_trylock", "critical"}]
    /\ (locked <=> holder /= NoHolder)
    /\ (holder /= NoHolder <=> pc[holder] = "critical")

Init ==
    /\ locked = FALSE
    /\ holder = NoHolder
    /\ pc = [t \in Thread |-> "idle"]

\* A thread decides to acquire the lock via the blocking lock() method.
StartLock(t) ==
    /\ pc[t] = "idle"
    /\ pc' = [pc EXCEPT ![t] = "attempt_lock"]
    /\ UNCHANGED <<locked, holder>>

\* A thread decides to acquire the lock via the non-blocking try_lock() method.
StartTryLock(t) ==
    /\ pc[t] = "idle"
    /\ pc' = [pc EXCEPT ![t] = "attempt_trylock"]
    /\ UNCHANGED <<locked, holder>>

\* A thread attempts the atomic compare-exchange operation. It succeeds.
\* This corresponds to the successful case of the loop in acquire_lock().
Acquire(t) ==
    /\ pc[t] = "attempt_lock"
    /\ \lnot locked
    /\ locked' = TRUE
    /\ holder' = t
    /\ pc' = [pc EXCEPT ![t] = "critical"]

\* A thread attempts the atomic compare-exchange, but it fails.
\* This corresponds to the spin_loop() hint and retrying the loop.
\* This is modeled as a stuttering step to allow other threads to proceed.
Spin(t) ==
    /\ pc[t] = "attempt_lock"
    /\ locked
    /\ UNCHANGED vars

\* A thread successfully acquires the lock via try_lock().
TryLockSuccess(t) ==
    /\ pc[t] = "attempt_trylock"
    /\ \lnot locked
    /\ locked' = TRUE
    /\ holder' = t
    /\ pc' = [pc EXCEPT ![t] = "critical"]

\* A thread fails to acquire the lock via try_lock() and moves on.
TryLockFail(t) ==
    /\ pc[t] = "attempt_trylock"
    /\ locked
    /\ pc' = [pc EXCEPT ![t] = "idle"]
    /\ UNCHANGED <<locked, holder>>

\* The thread in the critical section releases the lock (via SpinLockGuard's Drop).
Release(t) ==
    /\ pc[t] = "critical"
    /\ holder = t
    /\ locked' = FALSE
    /\ holder' = NoHolder
    /\ pc' = [pc EXCEPT ![t] = "idle"]

Next ==
    \E t \in Thread:
        \/ StartLock(t)
        \/ StartTryLock(t)
        \/ Acquire(t)
        \/ Spin(t)
        \/ TryLockSuccess(t)
        \/ TryLockFail(t)
        \/ Release(t)

Spec == Init /\ [][Next]_vars

\* The critical section is mutually exclusive.
MutualExclusion ==
    Cardinality({t \in Thread : pc[t] = "critical"}) <= 1

\* If a thread is trying to acquire a lock, it will eventually succeed,
\* assuming the lock is eventually released by any holder.
Liveness ==
    \A t \in Thread : (pc[t] = "attempt_lock") ~> (pc[t] = "critical")

====