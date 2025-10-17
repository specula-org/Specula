---- MODULE spin ----
EXTENDS Naturals, FiniteSets, Temporal
CONSTANT Threads
VARIABLES lock, pc

TypeOK == 
    lock \in BOOLEAN
    /\ pc \in [Threads -> {"idle", "locking", "try_locking", "locked", "unlocking"}]

Init == 
    lock = FALSE
    /\ pc = [t \in Threads |-> "idle"]

StartLock(t) == 
    pc[t] = "idle"
    /\ pc' = [pc EXCEPT ![t] = "locking"]
    /\ lock' = lock

StartTryLock(t) == 
    pc[t] = "idle"
    /\ pc' = [pc EXCEPT ![t] = "try_locking"]
    /\ lock' = lock

AttemptAcquire(t) == 
    /\ pc[t] \in {"locking", "try_locking"}
    /\ IF lock = FALSE
        THEN /\ lock' = TRUE
             /\ pc' = [pc EXCEPT ![t] = "locked"]
        ELSE /\ IF pc[t] = "locking"
                THEN pc' = [pc EXCEPT ![t] = "locking"]
                ELSE pc' = [pc EXCEPT ![t] = "idle"]
             /\ lock' = lock

Unlock(t) == 
    pc[t] = "locked"
    /\ lock' = FALSE
    /\ pc' = [pc EXCEPT ![t] = "idle"]

Next == 
    \E t \in Threads: 
        StartLock(t) 
        \/ StartTryLock(t)
        \/ AttemptAcquire(t)
        \/ Unlock(t)

Vars == <<lock, pc>>

Spec == 
    Init 
    /\ [][Next]_Vars 
    /\ \A t \in Threads: 
        WF_Vars(Unlock(t)) 
        /\ WF_Vars(AttemptAcquire(t))

====