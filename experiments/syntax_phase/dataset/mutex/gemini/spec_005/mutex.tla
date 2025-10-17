---- MODULE mutex ----
EXTENDS TLC, Sequences, Naturals, FiniteSets

CONSTANTS Threads

VARIABLES lock_held, lock_holder, wait_queue, thread_state

Nil == CHOOSE v : v \notin Threads
ThreadStates == {"idle", "wants_lock", "wants_try_lock", "in_cs", "waiting"}

vars == <<lock_held, lock_holder, wait_queue, thread_state>>

TypeOK ==
    /\ lock_held \in BOOLEAN
    /\ lock_holder \in Threads \cup {Nil}
    /\ wait_queue \in Seq(Threads)
    /\ thread_state \in [Threads -> ThreadStates]
    /\ (lock_held <=> lock_holder /= Nil)
    /\ (\A i, j \in DOMAIN wait_queue : i /= j => wait_queue[i] /= wait_queue[j])
    /\ (\A t \in Threads : (t \in Range(wait_queue)) <=> (thread_state[t] = "waiting"))

Init ==
    /\ lock_held = FALSE
    /\ lock_holder = Nil
    /\ wait_queue = <<>>
    /\ thread_state = [t \in Threads |-> "idle"]

RequestLock(t) ==
    /\ thread_state[t] = "idle"
    /\ thread_state' = [thread_state EXCEPT ![t] = "wants_lock"]
    /\ UNCHANGED <<lock_held, lock_holder, wait_queue>>

RequestTryLock(t) ==
    /\ thread_state[t] = "idle"
    /\ thread_state' = [thread_state EXCEPT ![t] = "wants_try_lock"]
    /\ UNCHANGED <<lock_held, lock_holder, wait_queue>>

Acquire(t) ==
    /\ thread_state[t] \in {"wants_lock", "wants_try_lock"}
    /\ \lnot lock_held
    /\ lock_held' = TRUE
    /\ lock_holder' = t
    /\ thread_state' = [thread_state EXCEPT ![t] = "in_cs"]
    /\ UNCHANGED <<wait_queue>>

Block(t) ==
    /\ thread_state[t] = "wants_lock"
    /\ lock_held
    /\ thread_state' = [thread_state EXCEPT ![t] = "waiting"]
    /\ wait_queue' = Append(wait_queue, t)
    /\ UNCHANGED <<lock_held, lock_holder>>

TryLockFail(t) ==
    /\ thread_state[t] = "wants_try_lock"
    /\ lock_held
    /\ thread_state' = [thread_state EXCEPT ![t] = "idle"]
    /\ UNCHANGED <<lock_held, lock_holder, wait_queue>>

Unlock(t) ==
    /\ thread_state[t] = "in_cs"
    /\ lock_holder = t
    /\ lock_held' = FALSE
    /\ lock_holder' = Nil
    /\ IF Len(wait_queue) > 0
       THEN LET woken_thread == Head(wait_queue)
            IN  wait_queue' = Tail(wait_queue)
                /\ thread_state' = [thread_state EXCEPT ![t] = "idle", ![woken_thread] = "wants_lock"]
       ELSE wait_queue' = wait_queue
            /\ thread_state' = [thread_state EXCEPT ![t] = "idle"]

Next ==
    \E t \in Threads:
        \/ RequestLock(t)
        \/ RequestTryLock(t)
        \/ Acquire(t)
        \/ Block(t)
        \/ TryLockFail(t)
        \/ Unlock(t)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

====