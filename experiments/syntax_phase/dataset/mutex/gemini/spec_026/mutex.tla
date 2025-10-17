---- MODULE mutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Threads, Nil

VARIABLES
    lock_state,
    lock_holder,
    wait_queue,
    thread_state

vars == <<lock_state, lock_holder, wait_queue, thread_state>>

TypeOK ==
    /\ lock_state \in BOOLEAN
    /\ lock_holder \in Threads \cup {Nil}
    /\ wait_queue \in Seq(Threads)
    /\ thread_state \in [Threads -> {"running", "waiting", "holding_lock"}]
    /\ (lock_state = FALSE) <=> (lock_holder = Nil)
    /\ \A t \in Threads : (lock_holder = t) <=> (thread_state[t] = "holding_lock")
    /\ \A t \in Threads : (t \in Ran(wait_queue)) <=> (thread_state[t] = "waiting")

Init ==
    /\ lock_state = FALSE
    /\ lock_holder = Nil
    /\ wait_queue = <<>>
    /\ thread_state = [t \in Threads |-> "running"]

\* A thread successfully acquires the lock.
\* This models the success case for both blocking lock() and non-blocking try_lock().
AcquireLock(t) ==
    /\ thread_state[t] = "running"
    /\ lock_state = FALSE
    /\ lock_state' = TRUE
    /\ lock_holder' = t
    /\ thread_state' = [thread_state EXCEPT ![t] = "holding_lock"]
    /\ UNCHANGED <<wait_queue>>

\* A thread attempts a non-blocking try_lock() when the lock is held and fails.
\* The thread remains in the "running" state and can try again or do other work.
TryLockFail(t) ==
    /\ thread_state[t] = "running"
    /\ lock_state = TRUE
    /\ UNCHANGED vars

\* A thread attempts a blocking lock() when the lock is held.
\* The thread is enqueued and its state becomes "waiting".
BlockOnLock(t) ==
    /\ thread_state[t] = "running"
    /\ lock_state = TRUE
    /\ wait_queue' = Append(wait_queue, t)
    /\ thread_state' = [thread_state EXCEPT ![t] = "waiting"]
    /\ UNCHANGED <<lock_state, lock_holder>>

\* The thread holding the lock releases it, modeling the MutexGuard being dropped.
\* If the wait queue is not empty, the next thread is woken up (FIFO).
Unlock(t) ==
    /\ thread_state[t] = "holding_lock"
    /\ lock_state' = FALSE
    /\ lock_holder' = Nil
    /\ IF wait_queue = <<>>
       THEN /\ wait_queue' = wait_queue
            /\ thread_state' = [thread_state EXCEPT ![t] = "running"]
       ELSE /\ LET woken_thread == Head(wait_queue) IN
                 /\ wait_queue' = Tail(wait_queue)
                 /\ thread_state' = [thread_state EXCEPT ![t] = "running",
                                                          ![woken_thread] = "running"]

Next ==
    \E t \in Threads :
        \/ AcquireLock(t)
        \/ TryLockFail(t)
        \/ BlockOnLock(t)
        \/ Unlock(t)

Spec == Init /\ [][Next]_vars /\ \A t \in Threads : WF_vars(Unlock(t))

====