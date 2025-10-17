---- MODULE mutex ----
EXTENDS TLC, Sequences, Naturals, FiniteSets
CONSTANTS Threads, NONE
ASSUME IsFiniteSet(Threads)
ASSUME NONE \notin Threads
VARIABLES holder, waitQueue
TypeOK == 
  /\ holder \in Threads \cup {NONE}
  /\ waitQueue \in Seq(Threads)
  /\ \A i \in DOMAIN waitQueue : waitQueue[i] \in Threads
Init == 
  /\ holder = NONE
  /\ waitQueue = << >>
Lock(t) == 
  /\ t # holder
  /\ t \notin Range(waitQueue)
  /\ IF holder = NONE
        THEN /\ holder' = t
             /\ UNCHANGED waitQueue
        ELSE /\ waitQueue' = Append(waitQueue, t)
             /\ UNCHANGED holder
TryLock(t) == 
  /\ t # holder
  /\ t \notin Range(waitQueue)
  /\ IF holder = NONE
        THEN /\ holder' = t
             /\ UNCHANGED waitQueue
        ELSE /\ UNCHANGED <<holder, waitQueue>>
Unlock(t) == 
  /\ holder = t
  /\ holder' = NONE
  /\ IF waitQueue # << >>
        THEN /\ waitQueue' = Tail(waitQueue)
        ELSE /\ UNCHANGED waitQueue
Next == \E t \in Threads : Lock(t) \/ TryLock(t) \/ Unlock(t)
Spec == 
  Init 
  /\ [][Next]_<<holder, waitQueue>>
  /\ WF_<<holder, waitQueue>>(Next)
====