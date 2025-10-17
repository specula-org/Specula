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

StartLock(t) ==
    /\ thread_state[t] = "idle"
    /\ thread_state' = [thread_state EXCEPT ![t] = "trying"]
    /\ thread_request_type' = [thread_request_type EXCEPT ![t] = "blocking"]
    /\ UNCHANGED <<lock_state, holder>>

StartTryLock(t) ==
    /\ thread_state[t] = "idle"
    /\ thread_state' = [thread_state EXCEPT ![t] = "trying"]
    /\ thread_request_type' = [thread_request_type EXCEPT ![t] = "nonblocking"]
    /\ UNCHANGED <<lock_state, holder>>

AcquireLock(t) ==
    /\ thread_state[t] = "trying"
    /\ lock_state = FALSE
    /\ lock_state' = TRUE
    /\ thread_state' = [thread_state EXCEPT ![t] = "locked"]
    /\ holder' = t
    /\ UNCHANGED thread_request_type

FailAcquireBlocking(t) ==
    /\ thread_state[t] = "trying"
    /\ thread_request_type[t] = "blocking"
    /\ lock_state = TRUE
    /\ thread_state' = [thread_state EXCEPT ![t] = "spinning"]
    /\ UNCHANGED <<lock_state, thread_request_type, holder>>

FailAcquireNonBlocking(t) ==
    /\ thread_state[t] = "trying"
    /\ thread_request_type[t] = "nonblocking"
    /\ lock_state = TRUE
    /\ thread_state' = [thread_state EXCEPT ![t] = "idle"]
    /\ UNCHANGED <<lock_state, thread_request_type, holder>>

RetryFromSpinning(t) ==
    /\ thread_state[t] = "spinning"
    /\ thread_state' = [thread_state EXCEPT ![t] = "trying"]
    /\ UNCHANGED <<lock_state, thread_request_type, holder>>

ReleaseLock(t) ==
    /\ thread_state[t] = "locked"
    /\ holder = t
    /\ lock_state' = FALSE
    /\ thread_state' = [thread_state EXCEPT ![t] = "idle"]
    /\ holder' = NULL
    /\ UNCHANGED thread_request_type

Next ==
    \E t \in Threads:
        \/ StartLock(t)
        \/ StartTryLock(t)
        \/ AcquireLock(t)
        \/ FailAcquireBlocking(t)
        \/ FailAcquireNonBlocking(t)
        \/ RetryFromSpinning(t)
        \/ ReleaseLock(t)

Spec == Init /\ [][Next]_Vars 
             /\ \A t \in Threads: WF_Vars(AcquireLock(t))
             /\ \A t \in Threads: WF_Vars(RetryFromSpinning(t))
             /\ \A t \in Threads: WF_Vars(ReleaseLock(t))

====