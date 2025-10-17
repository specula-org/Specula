---- MODULE mutex ----
EXTENDS Naturals, Sequences, FiniteSets, TLC
CONSTANTS Threads, NULL
ASSUME NULL \notin Threads
VARIABLES lock, owner, wait_queue
vars == <<lock, owner, wait_queue>>
TypeOK == 
    /\ lock \in BOOLEAN
    /\ owner \in (Threads \cup {NULL})
    /\ wait_queue \in Seq(Threads)
    /\ (lock = TRUE) <=> (owner # NULL)
    /\ owner \notin Range(wait_queue)
Init == 
    /\ lock = FALSE
    /\ owner = NULL
    /\ wait_queue = <<>>
TryLock(t) == 
    /\ t \notin Range(wait_queue)
    /\ IF lock = FALSE THEN
           lock' = TRUE /\
           owner' = t /\
           wait_queue' = wait_queue
       ELSE
           UNCHANGED lock /\
           UNCHANGED owner /\
           UNCHANGED wait_queue
       END IF
Lock(t) == 
    /\ t \notin Range(wait_queue)
    /\ IF lock = FALSE THEN
           lock' = TRUE /\
           owner' = t /\
           wait_queue' = wait_queue
       ELSE
           wait_queue' = Append(wait_queue, t) /\
           lock' = lock /\
           owner' = owner
       END IF
Unlock(t) == 
    /\ owner = t
    /\ t \notin Range(wait_queue)
    /\ lock' = FALSE
    /\ owner' = NULL
    /\ IF wait_queue # <<>> THEN
           wait_queue' = Tail(wait_queue)
       ELSE
           wait_queue' = wait_queue
       END IF
Next == 
    \/ \E t \in Threads : TryLock(t)
    \/ \E t \in Threads : Lock(t)
    \/ \E t \in Threads : Unlock(t)
UnlockAny == \E t \in Threads : Unlock(t)
Spec == Init /\ [][Next]_vars /\ WF_vars(UnlockAny)
====