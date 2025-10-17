---- MODULE spin ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Threads, LockData

VARIABLES lockState, threadStates, lockHolder, threadActions

(* Type definitions *)
ThreadStateType == {"idle", "trying", "spinning", "locked", "releasing"}
LockStateType == {"unlocked", "locked"}
ThreadActionType == {"none", "lock", "try_lock"}

TypeOK == 
    /\ lockState \in LockStateType
    /\ threadStates \in [Threads -> ThreadStateType]
    /\ lockHolder \in Threads \cup {NULL}
    /\ threadActions \in [Threads -> ThreadActionType]

Init == 
    /\ lockState = "unlocked"
    /\ threadStates = [t \in Threads |-> "idle"]
    /\ lockHolder = NULL
    /\ threadActions = [t \in Threads |-> "none"]

(* Core spinlock operations *)
AcquireLock(t) == 
    /\ threadStates[t] = "trying"
    /\ lockState = "unlocked"
    /\ lockState' = "locked"
    /\ lockHolder' = t
    /\ threadStates' = [threadStates EXCEPT ![t] = "locked"]
    /\ threadActions' = threadActions

FailAcquire(t) == 
    /\ threadStates[t] = "trying"
    /\ lockState = "locked"
    /\ threadActions[t] = "try_lock"
    /\ threadStates' = [threadStates EXCEPT ![t] = "idle"]
    /\ threadActions' = [threadActions EXCEPT ![t] = "none"]
    /\ UNCHANGED <<lockState, lockHolder>>

EnterSpinLoop(t) == 
    /\ threadStates[t] = "trying"
    /\ lockState = "locked"
    /\ threadActions[t] = "lock"
    /\ threadStates' = [threadStates EXCEPT ![t] = "spinning"]
    /\ UNCHANGED <<lockState, lockHolder, threadActions>>

SpinRetry(t) == 
    /\ threadStates[t] = "spinning"
    /\ threadStates' = [threadStates EXCEPT ![t] = "trying"]
    /\ UNCHANGED <<lockState, lockHolder, threadActions>>

ReleaseLock(t) == 
    /\ threadStates[t] = "releasing"
    /\ lockHolder = t
    /\ lockState' = "unlocked"
    /\ lockHolder' = NULL
    /\ threadStates' = [threadStates EXCEPT ![t] = "idle"]
    /\ threadActions' = [threadActions EXCEPT ![t] = "none"]

(* Thread initiation actions *)
StartLock(t) == 
    /\ threadStates[t] = "idle"
    /\ threadActions[t] = "none"
    /\ threadStates' = [threadStates EXCEPT ![t] = "trying"]
    /\ threadActions' = [threadActions EXCEPT ![t] = "lock"]
    /\ UNCHANGED <<lockState, lockHolder>>

StartTryLock(t) == 
    /\ threadStates[t] = "idle"
    /\ threadActions[t] = "none"
    /\ threadStates' = [threadStates EXCEPT ![t] = "trying"]
    /\ threadActions' = [threadActions EXCEPT ![t] = "try_lock"]
    /\ UNCHANGED <<lockState, lockHolder>>

(* Complete next-state relation *)
Next == 
    \/ \E t \in Threads: StartLock(t)
    \/ \E t \in Threads: StartTryLock(t)
    \/ \E t \in Threads: AcquireLock(t)
    \/ \E t \in Threads: FailAcquire(t)
    \/ \E t \in Threads: EnterSpinLoop(t)
    \/ \E t \in Threads: SpinRetry(t)
    \/ \E t \in Threads: ReleaseLock(t)

Spec == 
    /\ Init
    /\ [][Next]_<<lockState, threadStates, lockHolder, threadActions>>
    /\ \A t \in Threads: WF_<<lockState, threadStates, lockHolder, threadActions>>(AcquireLock(t))
    /\ \A t \in Threads: WF_<<lockState, threadStates, lockHolder, threadActions>>(ReleaseLock(t))
    /\ \A t \in Threads: WF_<<lockState, threadStates, lockHolder, threadActions>>(SpinRetry(t))

====