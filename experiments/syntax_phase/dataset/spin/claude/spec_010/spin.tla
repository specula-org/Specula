---- MODULE spin ----

EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Threads

VARIABLES 
    lock_state,
    thread_state,
    thread_request_type,
    holder

Vars == <<lock_state, thread_state, thread_request_type, holder>>

ThreadStates == {"idle", "trying", "spinning", "locked"}
RequestTypes == {"blocking", "nonblocking"}
NULL == "NULL"

TypeOK ==
    /\ lock_state \in BOOLEAN
    /\ thread_state \in [Threads -> ThreadStates]
    /\ thread_request_type \in [Threads -> RequestTypes]
    /\ holder \in Threads \cup {NULL}

Init ==
    /\ lock_state = FALSE
    /\ thread_state = [t \in Threads |-> "idle"]
    /\ thread_request_type = [t \in Threads |-> "blocking"]
    /\ holder = NULL

Lock(t) ==
    /\ thread_state[t] = "idle"
    /\ thread_state' = [thread_state EXCEPT ![t] = "trying"]
    /\ thread_request_type' = [thread_request_type EXCEPT ![t] = "blocking"]
    /\ UNCHANGED <<lock_state, holder>>

TryLock(t) ==
    /\ thread_state[t] = "idle"
    /\ thread_state' = [thread_state EXCEPT ![t] = "trying"]
    /\ thread_request_type' = [thread_request_type EXCEPT ![t] = "nonblocking"]
    /\ UNCHANGED <<lock_state, holder>>

AcquireSuccess(t) ==
    /\ thread_state[t] = "trying"
    /\ lock_state = FALSE
    /\ lock_state' = TRUE
    /\ thread_state' = [thread_state EXCEPT ![t] = "locked"]
    /\ holder' = t
    /\ UNCHANGED thread_request_type

AcquireFailBlocking(t) ==
    /\ thread_state[t] = "trying"
    /\ thread_request_type[t] = "blocking"
    /\ lock_state = TRUE
    /\ thread_state' = [thread_state EXCEPT ![t] = "spinning"]
    /\ UNCHANGED <<lock_state, thread_request_type, holder>>

AcquireFailNonBlocking(t) ==
    /\ thread_state[t] = "trying"
    /\ thread_request_type[t] = "nonblocking"
    /\ lock_state = TRUE
    /\ thread_state' = [thread_state EXCEPT ![t] = "idle"]
    /\ UNCHANGED <<lock_state, thread_request_type, holder>>

SpinRetry(t) ==
    /\ thread_state[t] = "spinning"
    /\ thread_state' = [thread_state EXCEPT ![t] = "trying"]
    /\ UNCHANGED <<lock_state, thread_request_type, holder>>

Unlock(t) ==
    /\ thread_state[t] = "locked"
    /\ holder = t
    /\ lock_state' = FALSE
    /\ thread_state' = [thread_state EXCEPT ![t] = "idle"]
    /\ holder' = NULL
    /\ UNCHANGED thread_request_type

Next ==
    \/ \E t \in Threads : Lock(t)
    \/ \E t \in Threads : TryLock(t)
    \/ \E t \in Threads : AcquireSuccess(t)
    \/ \E t \in Threads : AcquireFailBlocking(t)
    \/ \E t \in Threads : AcquireFailNonBlocking(t)
    \/ \E t \in Threads : SpinRetry(t)
    \/ \E t \in Threads : Unlock(t)

Spec == Init /\ [][Next]_Vars 
         /\ \A t \in Threads : WF_Vars(AcquireSuccess(t))
         /\ \A t \in Threads : WF_Vars(SpinRetry(t))
         /\ \A t \in Threads : WF_Vars(Unlock(t))

====