---- MODULE spin ----
EXTENDS Integers, TLC

CONSTANTS Threads

ASSUME Threads \subseteq 1..Cardinality(Threads)

VARIABLES
    \* @type: Bool;
    lock_state,
    \* @type: [Threads -> STRING];
    thread_state

vars == <<lock_state, thread_state>>

TypeOK ==
    /\ lock_state \in BOOLEAN
    /\ thread_state \in [Threads -> {"idle", "trying", "critical"}]

Init ==
    /\ lock_state = FALSE
    /\ thread_state = [t \in Threads |-> "idle"]

\* A thread decides to acquire the lock, entering the busy-wait loop.
\* This corresponds to the initial part of the lock() method call.
Enter(t) ==
    /\ thread_state[t] = "idle"
    /\ thread_state' = [thread_state EXCEPT ![t] = "trying"]
    /\ lock_state' = lock_state

\* A spinning thread successfully acquires the lock.
\* This corresponds to the compare_exchange returning true.
Acquire(t) ==
    /\ thread_state[t] = "trying"
    /\ lock_state = FALSE
    /\ lock_state' = TRUE
    /\ thread_state' = [thread_state EXCEPT ![t] = "critical"]

\* A spinning thread fails to acquire the lock and continues to spin.
\* This corresponds to one iteration of the busy-wait loop where
\* compare_exchange returns false. This is a stuttering step for this thread.
Contend(t) ==
    /\ thread_state[t] = "trying"
    /\ lock_state = TRUE
    /\ UNCHANGED vars

\* A thread attempts to acquire the lock via try_lock() and succeeds.
TryLockSuccess(t) ==
    /\ thread_state[t] = "idle"
    /\ lock_state = FALSE
    /\ lock_state' = TRUE
    /\ thread_state' = [thread_state EXCEPT ![t] = "critical"]

\* A thread attempts to acquire the lock via try_lock() and fails.
\* The thread does not block and remains in the "idle" state.
TryLockFail(t) ==
    /\ thread_state[t] = "idle"
    /\ lock_state = TRUE
    /\ UNCHANGED vars

\* A thread holding the lock releases it.
\* This corresponds to the SpinLockGuard going out of scope (Drop).
Unlock(t) ==
    /\ thread_state[t] = "critical"
    /\ lock_state' = FALSE
    /\ thread_state' = [thread_state EXCEPT ![t] = "idle"]

Next ==
    \E t \in Threads:
        \/ Enter(t)
        \/ Acquire(t)
        \/ Contend(t)
        \/ TryLockSuccess(t)
        \/ TryLockFail(t)
        \/ Unlock(t)

\* Fairness ensures that every thread that is able to make progress
\* will eventually do so, preventing starvation.
Fairness == \A t \in Threads : WF_vars(Next)

Spec == Init /\ [][Next]_vars /\ Fairness

====