---- MODULE mutex ----
EXTENDS Sequences, Naturals, FiniteSets, Temporal
CONSTANTS Threads, NULL
ASSUME NULL \notin Threads
VARIABLES lock, waitQueue, owner
vars == <<lock, waitQueue, owner>>
Init == 
    /\ lock = FALSE
    /\ waitQueue = <<>>
    /\ owner = NULL
TryLock(t) == 
    /\ lock = FALSE
    /\ lock' = TRUE
    /\ owner' = t
    /\ waitQueue' = waitQueue
Lock(t) == 
    \/ /\ lock = FALSE
       /\ lock' = TRUE
       /\ owner' = t
       /\ waitQueue' = waitQueue
    \/ /\ lock = TRUE
       /\ t \notin { waitQueue[i] : i \in DOMAIN waitQueue }
       /\ waitQueue' = Append(waitQueue, t)
       /\ UNCHANGED <<lock, owner>>
Unlock(t) == 
    /\ owner = t
    /\ lock' = FALSE
    /\ owner' = NULL
    /\ waitQueue' = waitQueue
WakeOne == 
    /\ lock = FALSE
    /\ waitQueue # <<>>
    /\ lock' = TRUE
    \E first \in Threads:
        /\ first = Head(waitQueue)
        /\ owner' = first
        /\ waitQueue' = Tail(waitQueue)
Next == 
    \/ \E t \in Threads : TryLock(t)
    \/ \E t \in Threads : Lock(t)
    \/ \E t \in Threads : Unlock(t)
    \/ WakeOne
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
====