
---- MODULE spin ----
EXTENDS Naturals, Temporal
CONSTANTS Threads

VARIABLES lock_state, thread_state, request_type

(* State definitions *)
States == {"idle", "trying", "spinning", "locked"}
RequestTypes == {"blocking", "non_blocking"}

TypeOK == 
    /\ lock_state \in BOOLEAN
    /\ thread_state \in [Threads -> States]
    /\ request_type \in [Threads -> RequestTypes]

Init == 
    /\ lock_state = FALSE
    /\ thread_state = [t \in Threads |-> "idle"]
    /\ request_type = [t \in Threads |-> "blocking"]

(* Blocking lock acquisition *)
Lock(t) == 
    /\ thread_state[t] = "idle"
    /\ request_type' = [request_type EXCEPT ![t] = "blocking"]
    /\ thread_state' = [thread_state EXCEPT ![t] = "trying"]
    /\ UNCHANGED lock_state

(* Non-blocking lock attempt *)
TryLock(t) == 
    /\ thread_state[t] = "idle"
    /\ request_type' = [request_type EXCEPT ![t] = "non_blocking"]
    /\ thread_state' = [thread_state EXCEPT ![t] = "trying"]
    /\ UNCHANGED lock_state

(* Successful CAS acquisition *)
Acquire(t) == 
    /\ thread_state[t] = "trying"
    /\ lock_state = FALSE
    /\ lock_state' = TRUE
    /\ thread_state' = [thread_state EXCEPT ![t] = "locked"]
    /\ UNCHANGED request_type

(* Failed CAS with spin retry *)
SpinRetry(t) == 
    /\ thread_state[t] = "trying"
    /\ lock_state = TRUE
    /\ request_type[t] = "blocking"
    /\ thread_state' = [thread_state EXCEPT ![t] = "spinning"]
    /\ UNCHANGED <<lock_state, request_type>>

(* Failed CAS with immediate return *)
FailImmediate(t) == 
    /\ thread_state[t] = "trying"
    /\ lock_state = TRUE
    /\ request_type[t] = "non_blocking"
    /\ thread_state' = [thread_state EXCEPT ![t] = "idle"]
    /\ UNCHANGED <<lock_state, request_type>>

(* Continuation of spin loop *)
ContinueSpin(t) == 
    /\ thread_state[t] = "spinning"
    /\ thread_state' = [thread_state EXCEPT ![t] = "trying"]
    /\ UNCHANGED <<lock_state, request_type>>

(* Lock release *)
Unlock(t) == 
    /\ thread_state[t] = "locked"
    /\ lock_state' = FALSE
    /\ thread_state' = [thread_state EXCEPT ![t] = "idle"]
    /\ UNCHANGED request_type

(* Next-state relation *)
Next == 
    \E t \in Threads: 
        Lock(t) \/ TryLock(t) \/ Acquire(t) \/ SpinRetry(t)
        \/ FailImmediate(t) \/ ContinueSpin(t) \/ Unlock(t)

Vars == <<lock_state, thread_state, request_type>>
WF_Vars(A) == WF_(Vars, A)

Spec == Init /\ [][Next]_Vars /\ \A t \in Threads : WF_Vars(Unlock(t))

====