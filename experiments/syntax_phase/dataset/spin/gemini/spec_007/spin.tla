---- MODULE spin ----
EXTENDS Integers, TLC

CONSTANTS Threads

VARIABLES
    lock_state,
    pc,
    protected_data

vars == <<lock_state, pc, protected_data>>

TypeOK ==
    /\ lock_state \in {"unlocked", "locked"}
    /\ pc \in [Threads -> {"idle", "wants_lock", "wants_trylock", "in_cs"}]
    /\ protected_data \in Int

Init ==
    /\ lock_state = "unlocked"
    /\ pc = [t \in Threads |-> "idle"]
    /\ protected_data = 0

StartLock(t) ==
    /\ pc[t] = "idle"
    /\ pc' = [pc EXCEPT ![t] = "wants_lock"]
    /\ UNCHANGED <<lock_state, protected_data>>

StartTryLock(t) ==
    /\ pc[t] = "idle"
    /\ pc' = [pc EXCEPT ![t] = "wants_trylock"]
    /\ UNCHANGED <<lock_state, protected_data>>

Acquire(t) ==
    /\ pc[t] \in {"wants_lock", "wants_trylock"}
    /\ lock_state = "unlocked"
    /\ lock_state' = "locked"
    /\ pc' = [pc EXCEPT ![t] = "in_cs"]
    /\ UNCHANGED <<protected_data>>

TryAcquireFailure(t) ==
    /\ pc[t] = "wants_trylock"
    /\ lock_state = "locked"
    /\ pc' = [pc EXCEPT ![t] = "idle"]
    /\ UNCHANGED <<lock_state, protected_data>>

WorkInCS(t) ==
    /\ pc[t] = "in_cs"
    /\ protected_data' = protected_data + 1
    /\ UNCHANGED <<lock_state, pc>>

Release(t) ==
    /\ pc[t] = "in_cs"
    /\ lock_state' = "unlocked"
    /\ pc' = [pc EXCEPT ![t] = "idle"]
    /\ UNCHANGED <<protected_data>>

Next ==
    \E t \in Threads:
        \/ StartLock(t)
        \/ StartTryLock(t)
        \/ Acquire(t)
        \/ TryAcquireFailure(t)
        \/ WorkInCS(t)
        \/ Release(t)

Spec == Init /\ [][Next]_vars

Fairness == \A t \in Threads:
    /\ WF_vars(Acquire(t))
    /\ WF_vars(TryAcquireFailure(t))
    /\ WF_vars(Release(t))

MutualExclusion ==
    Cardinality({t \in Threads : pc[t] = "in_cs"}) <= 1

LockEventuallyAcquired ==
    \A t \in Threads:
        (pc[t] = "wants_lock") ~> (pc[t] = "in_cs")

====