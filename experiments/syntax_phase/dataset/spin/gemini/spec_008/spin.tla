---- MODULE spin ----
EXTENDS Naturals, TLC

CONSTANTS Threads

VARIABLES lock_state, pc, protected_data

vars == <<lock_state, pc, protected_data>>

TypeOK ==
    /\ lock_state \in BOOLEAN
    /\ pc \in [Threads -> {"idle", "locking", "try_locking", "in_cs"}]
    /\ protected_data \in Nat

Init ==
    /\ lock_state = FALSE
    /\ pc = [t \in Threads |-> "idle"]
    /\ protected_data = 0

RequestLock(t) ==
    /\ pc[t] = "idle"
    /\ pc' = [pc EXCEPT ![t] = "locking"]
    /\ UNCHANGED <<lock_state, protected_data>>

Spin(t) ==
    /\ pc[t] = "locking"
    /\ IF lock_state = FALSE
       THEN /\ lock_state' = TRUE
            /\ pc' = [pc EXCEPT ![t] = "in_cs"]
            /\ UNCHANGED protected_data
       ELSE /\ pc' = pc
            /\ UNCHANGED <<lock_state, protected_data>>

RequestTryLock(t) ==
    /\ pc[t] = "idle"
    /\ pc' = [pc EXCEPT ![t] = "try_locking"]
    /\ UNCHANGED <<lock_state, protected_data>>

AttemptTryLock(t) ==
    /\ pc[t] = "try_locking"
    /\ IF lock_state = FALSE
       THEN /\ lock_state' = TRUE
            /\ pc' = [pc EXCEPT ![t] = "in_cs"]
       ELSE /\ pc' = [pc EXCEPT ![t] = "idle"]
            /\ UNCHANGED lock_state
    /\ UNCHANGED protected_data

ReleaseLock(t) ==
    /\ pc[t] = "in_cs"
    /\ lock_state' = FALSE
    /\ pc' = [pc EXCEPT ![t] = "idle"]
    /\ protected_data' = protected_data + 1
    /\ UNCHANGED <<>>

ThreadAction(t) ==
    \/ RequestLock(t)
    \/ Spin(t)
    \/ RequestTryLock(t)
    \/ AttemptTryLock(t)
    \/ ReleaseLock(t)

Next ==
    \E t \in Threads: ThreadAction(t)

Spec == Init /\ [][Next]_vars

MutualExclusion ==
    Cardinality({t \in Threads : pc[t] = "in_cs"}) <= 1

Liveness ==
    \A t \in Threads:
        (pc[t] = "locking") ~> (pc[t] = "in_cs")

Fairness == \A t \in Threads: WF_vars(ThreadAction(t))

====