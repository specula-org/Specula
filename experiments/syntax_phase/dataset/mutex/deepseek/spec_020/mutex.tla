---- MODULE mutex ----
EXTENDS Naturals, Sequences, FiniteSets
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
    /\ \/ /\ lock = FALSE
          /\ lock' = TRUE
          /\ owner' = t
          /\ wait_queue' = wait_queue
       \/ /\ lock = TRUE
          /\ UNCHANGED <<lock, owner, wait_queue>>
Lock(t) == 
    /\ t \notin Range(wait_queue)
    /\ \/ /\ lock = FALSE
          /\ lock' = TRUE
          /\ owner' = t
          /\ wait_queue' = wait_queue
       \/ /\ lock = TRUE
          /\ wait_queue' = Append(wait_queue, t)
          /\ UNCHANGED <<lock, owner>>
Unlock(t) == 
    /\ owner = t
    /\ t \notin Range(wait_queue)
    /\ \/ /\ wait_queue = <<>>
          /\ lock' = FALSE
          /\ owner' = NULL
          /\ wait_queue' = wait_queue
       \/ /\ wait_queue # <<>>
          /\ lock' = TRUE
          /\ owner' = Head(wait_queue)
          /\ wait_queue' = Tail(wait_queue)
Next == 
    \/ \E t \in Threads : TryLock(t)
    \/ \E t \in Threads : Lock(t)
    \/ \E t \in Threads : Unlock(t)
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
====