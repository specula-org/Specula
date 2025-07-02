---- MODULE SpinLock ----

EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Threads

VARIABLES
    lock,
    pc

vars == <<lock, pc>>

Init ==
    /\ lock = FALSE
    /\ pc = [t \in Threads |-> "idle"]

Try(t) ==
    /\ pc[t] = "idle"
    /\ pc' = [pc EXCEPT ![t] = "trying"]
    /\ UNCHANGED lock

Acquire(t) ==
    /\ pc[t] = "trying"
    /\ lock = FALSE
    /\ lock' = TRUE
    /\ pc' = [pc EXCEPT ![t] = "critical"] 
    
Spin(t) ==
    /\ pc[t] = "trying"
    /\ lock = TRUE
    /\ UNCHANGED vars 

Release(t) ==
    /\ pc[t] = "critical"
    /\ lock = TRUE
    /\ lock' = FALSE
    /\ pc' = [pc EXCEPT ![t] = "idle"]

Next ==
    \E t \in Threads:
        \/ Try(t)
        \/ Acquire(t)
        \/ Spin(t)  
        \/ Release(t)

Spec == Init /\ [][Next]_vars

====