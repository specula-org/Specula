---- MODULE mutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Threads, Nil

VARIABLES mutex_state, lock_holder, wait_queue, thread_state

vars == <<mutex_state, lock_holder, wait_queue, thread_state>>

TypeOK ==
    /\ mutex_state \in {"unlocked", "locked"}
    /\ lock_holder \in Threads \cup {Nil}
    /\ wait_queue \in Seq(Threads)
    /\ thread_state \in [Threads -> {"idle", "waiting", "critical"}]
    /\ \A i, j \in DOMAIN wait_queue : i /= j => wait_queue[i] /= wait_queue[j]

Init ==
    /\ mutex_state = "unlocked"
    /\ lock_holder = Nil
    /\ wait_queue = <<>>
    /\ thread_state = [t \in Threads |-> "idle"]

TryLock(t) ==
    /\ thread_state[t] = "idle"
    /\ mutex_state = "unlocked"
    /\ mutex_state' = "locked"
    /\ lock_holder' = t
    /\ thread_state' = [thread_state EXCEPT ![t] = "critical"]
    /\ UNCHANGED <<wait_queue>>

TryLockFail(t) ==
    /\ thread_state[t] = "idle"
    /\ mutex_state = "locked"
    /\ UNCHANGED vars

LockAcquire(t) ==
    /\ thread_state[t] = "idle"
    /\ mutex_state = "unlocked"
    /\ mutex_state' = "locked"
    /\ lock_holder' = t
    /\ thread_state' = [thread_state EXCEPT ![t] = "critical"]
    /\ UNCHANGED <<wait_queue>>

LockBlock(t) ==
    /\ thread_state[t] = "idle"
    /\ mutex_state = "locked"
    /\ t \notin Set(wait_queue)
    /\ wait_queue' = Append(wait_queue, t)
    /\ thread_state' = [thread_state EXCEPT ![t] = "waiting"]
    /\ UNCHANGED <<mutex_state, lock_holder>>

Unlock(t) ==
    /\ thread_state[t] = "critical"
    /\ lock_holder = t
    /\ mutex_state' = "unlocked"
    /\ lock_holder' = Nil
    /\ IF wait_queue = <<>>
       THEN /\ wait_queue' = wait_queue
            /\ thread_state' = [thread_state EXCEPT ![t] = "idle"]
       ELSE /\ LET woken_thread == Head(wait_queue)
              IN thread_state' = [thread_state EXCEPT ![t] = "idle", ![woken_thread] = "idle"]
            /\ wait_queue' = Tail(wait_queue)

Next ==
    \E t \in Threads :
        \/ TryLock(t)
        \/ TryLockFail(t)
        \/ LockAcquire(t)
        \/ LockBlock(t)
        \/ Unlock(t)

Fairness ==
    \A t \in Threads :
        /\ WF_vars(Unlock(t))
        /\ WF_vars(LockAcquire(t) \/ LockBlock(t))

Spec == Init /\ [][Next]_vars /\ Fairness

====