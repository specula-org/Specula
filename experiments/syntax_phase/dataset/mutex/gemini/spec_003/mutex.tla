---- MODULE mutex ----
EXTENDS TLC, Sequences, Naturals, FiniteSets

CONSTANTS Threads, NIL

VARIABLES mutex_locked, lock_holder, wait_queue, thread_state

vars == <<mutex_locked, lock_holder, wait_queue, thread_state>>

TypeOK ==
    /\ mutex_locked \in BOOLEAN
    /\ lock_holder \in Threads \cup {NIL}
    /\ wait_queue \in Seq(Threads)
    /\ thread_state \in [Threads -> {"idle", "holding", "waiting"}]

Init ==
    /\ mutex_locked = FALSE
    /\ lock_holder = NIL
    /\ wait_queue = <<>>
    /\ thread_state = [t \in Threads |-> "idle"]

\* A thread successfully acquires the lock. This models an uncontended
\* lock() or a successful try_lock().
AcquireLock(t) ==
    /\ thread_state[t] = "idle"
    /\ \lnot mutex_locked
    /\ mutex_locked' = TRUE
    /\ lock_holder' = t
    /\ thread_state' = [thread_state EXCEPT ![t] = "holding"]
    /\ UNCHANGED <<wait_queue>>

\* A thread's non-blocking try_lock() fails because the lock is held.
\* The thread remains idle and can try again later or do other work.
TryLockFail(t) ==
    /\ thread_state[t] = "idle"
    /\ mutex_locked
    /\ UNCHANGED vars

\* A thread attempts a blocking lock() while the lock is held.
\* It is enqueued and its state changes to "waiting".
BlockOnLock(t) ==
    /\ thread_state[t] = "idle"
    /\ mutex_locked
    /\ wait_queue' = Append(wait_queue, t)
    /\ thread_state' = [thread_state EXCEPT ![t] = "waiting"]
    /\ UNCHANGED <<mutex_locked, lock_holder>>

\* The thread holding the lock releases it. This corresponds to the
\* MutexGuard being dropped. If the wait queue is not empty, the
\* thread at the head of the queue is woken up (its state becomes "idle").
Unlock(t) ==
    /\ thread_state[t] = "holding"
    /\ lock_holder = t
    /\ mutex_locked' = FALSE
    /\ lock_holder' = NIL
    /\ IF Len(wait_queue) > 0 THEN
        (/\ LET woken_thread == Head(wait_queue)
              IN  thread_state' = [thread_state EXCEPT ![t] = "idle", ![woken_thread] = "idle"]
         /\ wait_queue' = Tail(wait_queue) )
    ELSE
        (/\ thread_state' = [thread_state EXCEPT ![t] = "idle"]
         /\ wait_queue' = wait_queue )

Next ==
    \E t \in Threads :
        \/ AcquireLock(t)
        \/ TryLockFail(t)
        \/ BlockOnLock(t)
        \/ Unlock(t)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

====