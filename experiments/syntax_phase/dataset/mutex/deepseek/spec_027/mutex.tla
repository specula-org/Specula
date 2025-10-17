---- MODULE mutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags
CONSTANT Threads
ASSUME IsFiniteSet(Threads)
VARIABLES holder, waitQueue
TypeOK == 
  /\ holder \in (Threads \cup {NONE})  \* FIXED: Removed extra closing parenthesis
  /\ waitQueue \in Seq(Threads)
  /\ \A i \in DOMAIN waitQueue : waitQueue[i] \in Threads
Init == 
  /\ holder = NONE
  /\ waitQueue = << >>
Lock(t) == 
  /\ t # holder  \* FIXED: Changed \neq to # syntax
  /\ t \notin Range(waitQueue)
  /\ IF holder = NONE THEN
        /\ holder' = t
        /\ waitQueue' = waitQueue
     ELSE
        /\ waitQueue' = Append(waitQueue, t)
        /\ holder' = holder
     END IF
TryLock(t) == 
  /\ t # holder  \* FIXED: Changed \neq to # syntax
  /\ t \notin Range(waitQueue)
  /\ IF holder = NONE THEN
        /\ holder' = t
        /\ waitQueue' = waitQueue
     ELSE
        /\ UNCHANGED <<holder, waitQueue>>
     END IF
Unlock(t) == 
  /\ holder = t
  /\ holder' = NONE
  /\ IF waitQueue /= << >> THEN
        /\ waitQueue' = Tail(waitQueue)
     ELSE
        /\ waitQueue' = waitQueue
     END IF
Next == \E t \in Threads : Lock(t) \/ TryLock(t) \/ Unlock(t)
Spec == 
  Init 
  /\ [][Next]_<<holder, waitQueue>>
  /\ \A t \in Threads : WF_<<holder, waitQueue>>(Unlock(t))
  /\ \A t \in Threads : WF_<<holder, waitQueue>>(Lock(t))
====