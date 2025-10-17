---- MODULE mutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Threads, NULL

VARIABLES 
    mutex_locked,
    thread_states,
    wait_queue,
    guards,
    lock_holder

vars == <<mutex_locked, thread_states, wait_queue, guards, lock_holder>>

ThreadStates == {"Running", "Waiting"}

TypeOK ==
    /\ mutex_locked \in BOOLEAN
    /\ thread_states \in [Threads -> ThreadStates]
    /\ wait_queue \in Seq(Threads)
    /\ guards \in [Threads -> BOOLEAN]
    /\ lock_holder \in Threads \cup {NULL}

Init == 
    /\ mutex_locked = FALSE
    /\ thread_states = [t \in Threads |-> "Running"]
    /\ wait_queue = <<>>
    /\ guards = [t \in Threads |-> FALSE]
    /\ lock_holder = NULL

CAS(thread, expected, new) ==
    /\ mutex_locked = expected
    /\ mutex_locked' = new
    /\ IF new THEN lock_holder' = thread ELSE lock_holder' = NULL
    /\ UNCHANGED <<thread_states, wait_queue, guards>>

Store(value) ==
    /\ mutex_locked' = value
    /\ IF ~value THEN lock_holder' = NULL ELSE UNCHANGED lock_holder
    /\ UNCHANGED <<thread_states, wait_queue, guards>>

EnterWaitQueue(thread) ==
    /\ thread_states[thread] = "Running"
    /\ thread_states' = [thread_states EXCEPT ![thread] = "Waiting"]
    /\ wait_queue' = Append(wait_queue, thread)
    /\ UNCHANGED <<mutex_locked, guards, lock_holder>>

WakeOne ==
    /\ Len(wait_queue) > 0
    /\ LET woken == Head(wait_queue) IN
        /\ thread_states' = [thread_states EXCEPT ![woken] = "Running"]
        /\ wait_queue' = Tail(wait_queue)
    /\ UNCHANGED <<mutex_locked, guards, lock_holder>>

CreateGuard(thread) ==
    /\ ~guards[thread]
    /\ guards' = [guards EXCEPT ![thread] = TRUE]
    /\ UNCHANGED <<mutex_locked, thread_states, wait_queue, lock_holder>>

DestroyGuard(thread) ==
    /\ guards[thread]
    /\ guards' = [guards EXCEPT ![thread] = FALSE]
    /\ UNCHANGED <<mutex_locked, thread_states, wait_queue, lock_holder>>

TryLock(thread) ==
    /\ thread_states[thread] = "Running"
    /\ ~guards[thread]
    /\ IF ~mutex_locked THEN
        /\ CAS(thread, FALSE, TRUE)
        /\ CreateGuard(thread)'
       ELSE
        /\ UNCHANGED vars

Lock(thread) ==
    /\ thread_states[thread] = "Running"
    /\ ~guards[thread]
    /\ IF ~mutex_locked THEN
        /\ CAS(thread, FALSE, TRUE)
        /\ CreateGuard(thread)'
       ELSE
        /\ EnterWaitQueue(thread)

AcquireAfterWake(thread) ==
    /\ thread_states[thread] = "Running"
    /\ ~guards[thread]
    /\ ~mutex_locked
    /\ CAS(thread, FALSE, TRUE)
    /\ CreateGuard(thread)'

Unlock(thread) ==
    /\ guards[thread]
    /\ lock_holder = thread
    /\ DestroyGuard(thread)'
    /\ Store(FALSE)'
    /\ IF Len(wait_queue) > 0 THEN WakeOne' ELSE UNCHANGED <<thread_states, wait_queue>>

Next == 
    \/ \E thread \in Threads : TryLock(thread)
    \/ \E thread \in Threads : Lock(thread)
    \/ \E thread \in Threads : AcquireAfterWake(thread)
    \/ \E thread \in Threads : Unlock(thread)

Spec == Init /\ [][Next]_vars /\ WF_vars(\E t \in Threads : Unlock(t)) /\ WF_vars(\E t \in Threads : AcquireAfterWake(t))

====