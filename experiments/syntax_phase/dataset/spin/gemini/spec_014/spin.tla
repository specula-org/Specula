---- MODULE spin ----
EXTENDS Integers, TLC

CONSTANTS Proc, Nil

ASSUME Nil \notin Proc

VARIABLES lock_state, lock_holder, pc

vars == <<lock_state, lock_holder, pc>>

TypeOK ==
    /\ lock_state \in BOOLEAN
    /\ lock_holder \in Proc \cup {Nil}
    /\ pc \in [Proc -> {"idle", "req_lock", "req_trylock", "spinning", "critical"}]

Init ==
    /\ lock_state = FALSE
    /\ lock_holder = Nil
    /\ pc = [p \in Proc |-> "idle"]

RequestLock(p) ==
    /\ pc[p] = "idle"
    /\ pc' = [pc EXCEPT ![p] = "req_lock"]
    /\ UNCHANGED <<lock_state, lock_holder>>

RequestTryLock(p) ==
    /\ pc[p] = "idle"
    /\ pc' = [pc EXCEPT ![p] = "req_trylock"]
    /\ UNCHANGED <<lock_state, lock_holder>>

AttemptAcquire(p) ==
    /\ pc[p] \in {"req_lock", "req_trylock", "spinning"}
    /\ IF lock_state = FALSE THEN
        /\ lock_state' = TRUE
        /\ lock_holder' = p
        /\ pc' = [pc EXCEPT ![p] = "critical"]
    ELSE
        /\ (IF pc[p] \in {"req_lock", "spinning"}
            THEN pc' = [pc EXCEPT ![p] = "spinning"]
            ELSE pc' = [pc EXCEPT ![p] = "idle"])
        /\ UNCHANGED <<lock_state, lock_holder>>

ReleaseLock(p) ==
    /\ pc[p] = "critical"
    /\ lock_holder = p
    /\ lock_state' = FALSE
    /\ lock_holder' = Nil
    /\ pc' = [pc EXCEPT ![p] = "idle"]

Next ==
    \E p \in Proc:
        \/ RequestLock(p)
        \/ RequestTryLock(p)
        \/ AttemptAcquire(p)
        \/ ReleaseLock(p)

Spec == Init /\ [][Next]_vars

====