---- MODULE spin ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Threads

VARIABLES 
    lock_state,
    thread_state,
    request_type

vars == <<lock_state, thread_state, request_type, has_guard>>

ThreadStates == {"idle", "trying", "spinning", "locked"}
RequestTypes == {"blocking", "non_blocking"}

TypeOK ==
    /\ lock_state \in BOOLEAN
    /\ thread_state \in [Threads -> ThreadStates]
    /\ request_type \in [Threads -> RequestTypes]
    /\ has_guard \in [Threads -> BOOLEAN]

Init == 
    /\ lock_state = FALSE
    /\ thread_state = [t \in Threads |-> "idle"]
    /\ request_type = [t \in Threads |-> "blocking"]
    /\ has_guard = [t \in Threads |-> FALSE]

Lock(t) ==
    /\ thread_state[t] = "idle"
    /\ thread_state' = [thread_state EXCEPT ![t] = "trying"]
    /\ request_type' = [request_type EXCEPT ![t] = "blocking"]
    /\ UNCHANGED <<lock_state, has_guard>>

TryLock(t) ==
    /\ thread_state[t] = "idle"
    /\ thread_state' = [thread_state EXCEPT ![t] = "trying"]
    /\ request_type' = [request_type EXCEPT ![t] = "non_blocking"]
    /\ UNCHANGED <<lock_state, has_guard>>

CompareExchangeSuccess(t) ==
    /\ thread_state[t] = "trying"
    /\ lock_state = FALSE
    /\ lock_state' = TRUE
    /\ thread_state' = [thread_state EXCEPT ![t] = "locked"]
    /\ has_guard' = [has_guard EXCEPT ![t] = TRUE]
    /\ UNCHANGED request_type

CompareExchangeFailBlocking(t) ==
    /\ thread_state[t] = "trying"
    /\ lock_state = TRUE
    /\ request_type[t] = "blocking"
    /\ thread_state' = [thread_state EXCEPT ![t] = "spinning"]
    /\ UNCHANGED <<lock_state, request_type, has_guard>>

CompareExchangeFailNonBlocking(t) ==
    /\ thread_state[t] = "trying"
    /\ lock_state = TRUE
    /\ request_type[t] = "non_blocking"
    /\ thread_state' = [thread_state EXCEPT ![t] = "idle"]
    /\ UNCHANGED <<lock_state, request_type, has_guard>>

Spin(t) ==
    /\ thread_state[t] = "spinning"
    /\ request_type[t] = "blocking"
    /\ thread_state' = [thread_state EXCEPT ![t] = "trying"]
    /\ UNCHANGED <<lock_state, request_type, has_guard>>

Unlock(t) ==
    /\ thread_state[t] = "locked"
    /\ has_guard[t] = TRUE
    /\ lock_state' = FALSE
    /\ thread_state' = [thread_state EXCEPT ![t] = "idle"]
    /\ has_guard' = [has_guard EXCEPT ![t] = FALSE]
    /\ UNCHANGED request_type

Next == 
    \/ \E t \in Threads : Lock(t)
    \/ \E t \in Threads : TryLock(t)
    \/ \E t \in Threads : CompareExchangeSuccess(t)
    \/ \E t \in Threads : CompareExchangeFailBlocking(t)
    \/ \E t \in Threads : CompareExchangeFailNonBlocking(t)
    \/ \E t \in Threads : Spin(t)
    \/ \E t \in Threads : Unlock(t)

Spec == Init /\ [][Next]_vars /\ WF_vars(\E t \in Threads : CompareExchangeSuccess(t)) /\ WF_vars(\E t \in Threads : Spin(t))

====