---- MODULE mutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags
CONSTANTS Threads, NULL
ASSUME NULL \notin Threads
VARIABLES locked, holder, waitQueue

TypeOK == 
  /\ locked \in BOOLEAN
  /\ holder \in Threads \cup {NULL}
  /\ waitQueue \in Seq(Threads)
  /\ \A i \in 1..Len(waitQueue) : \A j \in 1..Len(waitQueue) : i /= j => waitQueue[i] /= waitQueue[j]  \* FIX: Replaced \neq with /= for ASCII compatibility
  /\ holder \notin { waitQueue[i] : i \in 1..Len(waitQueue) }
  /\ (locked = TRUE) => (holder \in Threads)
  /\ (locked = FALSE) => (holder = NULL)

Init == 
  /\ locked = FALSE
  /\ holder = NULL
  /\ waitQueue = << >>

TryAcquire(t) == 
  /\ locked = FALSE
  /\ holder' = t
  /\ locked' = TRUE
  /\ waitQueue' = waitQueue

BlockingAcquire(t) == 
  /\ locked = TRUE
  /\ \neg (\E i \in 1..Len(waitQueue) : waitQueue[i] = t)
  /\ waitQueue' = Append(waitQueue, t)
  /\ UNCHANGED <<locked, holder>>

Release(t) == 
  /\ holder = t
  /\ IF waitQueue \neq <<>> THEN
        LET first == Head(waitQueue) IN
        /\ holder' = first
        /\ locked' = TRUE
        /\ waitQueue' = Tail(waitQueue)
     ELSE
        /\ holder' = NULL
        /\ locked' = FALSE
        /\ waitQueue' = waitQueue

Next == 
  \/ \E t \in Threads : TryAcquire(t)
  \/ \E t \in Threads : BlockingAcquire(t)
  \/ \E t \in Threads : Release(t)

vars == <<locked, holder, waitQueue>>

Spec == Init /\ [][Next]_vars /\ \A t \in Threads : WF_vars(Release(t))
====