
---- MODULE spin ----
VARIABLES lock, pc

TypeOK == 
    /\ lock \in BOOLEAN
    /\ pc \in [Threads -> {"idle", "trying", "locked"}]
    /\ (lock <=> (\E t \in Threads: pc[t] = "locked"))

Init == 
    /\ lock = FALSE
    /\ pc = [t \in Threads |-> "idle"]

StartLock(t) == 
    /\ pc[t] = "idle"
    /\ pc' = [pc EXCEPT ![t] = "trying"]
    /\ lock' = lock

TryLock(t) == 
    /\ pc[t] = "trying"
    /\ IF lock = FALSE
        THEN /\ lock' = TRUE
             /\ pc' = [pc EXCEPT ![t] = "locked"]
        ELSE /\ lock' = lock
             /\ pc' = [pc EXCEPT ![t] = "trying"]

TryLock_Immediate(t) == 
    /\ pc[t] = "idle"
    /\ IF lock = FALSE
        THEN /\ lock' = TRUE
             /\ pc' = [pc EXCEPT ![t] = "locked"]
        ELSE /\ lock' = lock
             /\ pc' = [pc EXCEPT ![t] = "idle"]

Unlock(t) == 
    /\ pc[t] = "locked"
    /\ lock' = FALSE
    /\ pc' = [pc EXCEPT ![t] = "idle"]

Next == 
    \E t \in Threads: 
        StartLock(t) \/ TryLock(t) \/ TryLock_Immediate(t) \/ Unlock(t)

Vars == <<lock, pc>>

Spec == 
    Init 
    /\ [][Next]_Vars 
    /\ WF_Vars(Next)

====