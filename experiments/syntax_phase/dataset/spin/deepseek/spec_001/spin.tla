---- MODULE spin ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANT Threads
CONSTANT MaxAttempts

VARIABLES lock_state, thread_states, attempts

(* Type correctness invariant *)
TypeOK == 
    /\ lock_state \in {TRUE, FALSE}
    /\ thread_states \in [Threads -> {"idle", "trying", "spinning", "locked"}]
    /\ attempts \in [Threads -> 0..MaxAttempts]

(* Initial state *)
Init == 
    /\ lock_state = FALSE
    /\ thread_states = [t \in Threads |-> "idle"]
    /\ attempts = [t \in Threads |-> 0]

(* Lock acquisition attempt - common for both lock() and try_lock() *)
TryAcquireLock(t) ==
    /\ thread_states[t] \in {"trying", "spinning"}
    /\ lock_state = FALSE
    /\ thread_states' = [thread_states EXCEPT ![t] = "locked"]
    /\ lock_state' = TRUE
    /\ attempts' = [attempts EXCEPT ![t] = 0]
    /\ UNCHANGED <<>>

(* Failed CAS operation - different behavior based on request type *)
FailedAcquisition(t) ==
    /\ thread_states[t] = "trying"
    /\ lock_state = TRUE
    /\ attempts[t] < MaxAttempts
    /\ attempts' = [attempts EXCEPT ![t] = attempts[t] + 1]
    /\ thread_states' = [thread_states EXCEPT ![t] = "spinning"]
    /\ UNCHANGED <<lock_state>>

(* Non-blocking try_lock() gives up on failure *)
TryLockGiveUp(t) ==
    /\ thread_states[t] = "trying"  
    /\ lock_state = TRUE
    /\ thread_states' = [thread_states EXCEPT ![t] = "idle"]
    /\ attempts' = [attempts EXCEPT ![t] = 0]
    /\ UNCHANGED <<lock_state>>

(* Spinning thread retries acquisition *)
SpinRetry(t) ==
    /\ thread_states[t] = "spinning"
    /\ lock_state = TRUE
    /\ thread_states' = [thread_states EXCEPT ![t] = "trying"]
    /\ UNCHANGED <<lock_state, attempts>>

(* Release lock *)
ReleaseLock(t) ==
    /\ thread_states[t] = "locked"
    /\ thread_states' = [thread_states EXCEPT ![t] = "idle"]
    /\ lock_state' = FALSE
    /\ UNCHANGED <<attempts>>

(* Blocking lock() request *)
LockRequest(t) ==
    /\ thread_states[t] = "idle"
    /\ thread_states' = [thread_states EXCEPT ![t] = "trying"]
    /\ UNCHANGED <<lock_state, attempts>>

(* Non-blocking try_lock() request *)
TryLockRequest(t) ==
    /\ thread_states[t] = "idle"
    /\ thread_states' = [thread_states EXCEPT ![t] = "trying"]
    /\ UNCHANGED <<lock_state, attempts>>

(* Next state relation *)
Next ==
    \/ \E t \in Threads: TryAcquireLock(t)
    \/ \E t \in Threads: FailedAcquisition(t)
    \/ \E t \in Threads: TryLockGiveUp(t)
    \/ \E t \in Threads: SpinRetry(t)
    \/ \E t \in Threads: ReleaseLock(t)
    \/ \E t \in Threads: LockRequest(t)
    \/ \E t \in Threads: TryLockRequest(t)

(* Specification with fairness assumptions *)
Spec == 
    Init 
    /\ [][Next]_<<lock_state, thread_states, attempts>>
    /\ WF_<<lock_state, thread_states, attempts>>(TryAcquireLock(_))
    /\ WF_<<lock_state, thread_states, attempts>>(ReleaseLock(_))
    /\ WF_<<lock_state, thread_states, attempts>>(LockRequest(_))
    /\ WF_<<lock_state, thread_states, attempts>>(TryLockRequest(_))

====