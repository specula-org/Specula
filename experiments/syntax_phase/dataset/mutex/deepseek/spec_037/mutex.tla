---- MODULE mutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags
CONSTANTS Threads, NULL
ASSUME Threads /= {}
VARIABLES lock, holder, waitQueue

vars == <<lock, holder, waitQueue>>

TypeOK == 
  /\ lock \in BOOLEAN
  /\ holder \in (Threads \cup {NULL})
  /\ waitQueue \in Seq(Threads)
  /\ (lock = TRUE) <=> (holder /= NULL)
  /\ \A t \in Threads : t \in Ran(waitQueue) => holder /= t

Init == 
  /\ lock = FALSE
  /\ holder = NULL
  /\ waitQueue = << >>

LockAcquire(thread) == 
  /\ lock = FALSE
  /\ lock' = TRUE
  /\ holder' = thread
  /\ waitQueue' = waitQueue

EnterQueue(thread) == 
  /\ lock = TRUE
  /\ waitQueue' = Append(waitQueue, thread)
  /\ UNCHANGED <<lock, holder>>

LockAttempt(thread) == 
  \/ LockAcquire(thread)
  \/ EnterQueue(thread)

TryLock(thread) == 
  \/ LockAcquire(thread)
  \/ /\ lock = TRUE
     /\ UNCHANGED <<lock, holder, waitQueue>>

Unlock(thread) == 
  /\ holder = thread
  /\ IF waitQueue /= << >> THEN
       /\ lock' = TRUE
       /\ holder' = Head(waitQueue)
       /\ waitQueue' = Tail(waitQueue)
     ELSE
       /\ lock' = FALSE
       /\ holder' = NULL
       /\ waitQueue' = waitQueue

Action(thread) == 
  LockAttempt(thread) \/ TryLock(thread) \/ Unlock(thread)

Next == 
  \E thread \in Threads : Action(thread)

Spec == 
  Init 
  /\ [][Next]_vars 
  /\ \A thread \in Threads : WF_vars(Unlock(thread))

====