
---- MODULE mutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags
CONSTANTS Threads
VARIABLES lock, waitQueue, holder

TypeOK == 
  lock \in BOOLEAN
  /\ waitQueue \in Seq(Threads)
  /\ holder \subseteq Threads
  /\ (holder = {} \/ \E t \in Threads: holder = {t})
  /\ (lock <=> holder # {})
  /\ \A t \in Threads: ~(t \in holder /\ t \in Range(waitQueue))

Init == 
  lock = FALSE
  /\ waitQueue = <<>>
  /\ holder = {}

Lock(t) == 
  /\ t \notin holder
  /\ t \notin Range(waitQueue)
  /\ IF lock
      THEN /\ waitQueue' = Append(waitQueue, t)
           /\ UNCHANGED <<lock, holder>>
      ELSE /\ lock' = TRUE
           /\ holder' = {t}
           /\ waitQueue' = waitQueue

TryLock(t) == 
  /\ t \notin holder
  /\ t \notin Range(waitQueue)
  /\ IF ~lock
      THEN /\ lock' = TRUE
           /\ holder' = {t}
      ELSE /\ UNCHANGED <<lock, holder>>
  /\ UNCHANGED <<waitQueue>>

Unlock(t) == 
  /\ holder = {t}
  /\ \/ /\ waitQueue = <<>>
         /\ lock' = FALSE
         /\ holder' = {}
         /\ UNCHANGED waitQueue
      \/ /\ waitQueue # <<>>
         /\ LET t2 == Head(waitQueue) IN
            /\ lock' = TRUE
            /\ holder' = {t2}
            /\ waitQueue' = Tail(waitQueue)

Next == \E t \in Threads: Lock(t) \/ TryLock(t) \/ Unlock(t)
Vars == <<lock, waitQueue, holder>>
Spec == Init /\ [][Next]_Vars /\ WF_Vars(Next)
====