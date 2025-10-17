---- MODULE mutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags
CONSTANTS Threads, NULL
ASSUME NULL ∉ Threads
VARIABLES lock, waitQueue, criticalThread
TypeOK == 
  /\ lock ∈ BOOLEAN
  /\ waitQueue ∈ Seq(Threads)
  /\ criticalThread ∈ Threads ∪ {NULL}
  /\ (lock = TRUE) ≡ (criticalThread ≠ NULL)
Init == 
  /\ lock = FALSE
  /\ waitQueue = << >>
  /\ criticalThread = NULL
TryLock(t) == 
  /\ t ∈ Threads
  /\ criticalThread ≠ t
  /\ t ∉ waitQueue
  /\ lock = FALSE
  /\ lock' = TRUE
  /\ criticalThread' = t
  /\ waitQueue' = waitQueue
Lock(t) == 
  /\ t ∈ Threads
  /\ criticalThread ≠ t
  /\ t ∉ waitQueue
  /\ ( \/ (lock = FALSE /\ lock' = TRUE /\ criticalThread' = t /\ waitQueue' = waitQueue)
      \/ (lock = TRUE /\ waitQueue' = Append(waitQueue, t) /\ UNCHANGED <<lock, criticalThread>>)
    )
Unlock(t) == 
  /\ t ∈ Threads
  /\ criticalThread = t
  /\ lock = TRUE
  /\ IF waitQueue ≠ << >> THEN
        /\ lock' = TRUE
        /\ criticalThread' = Head(waitQueue)
        /\ waitQueue' = Tail(waitQueue)
      ELSE
        /\ lock' = FALSE
        /\ criticalThread' = NULL
        /\ waitQueue' = waitQueue
Next == ∃ t ∈ Threads : (TryLock(t) \/ Lock(t) \/ Unlock(t))
WF_Unlock(t) == WF_<<lock, waitQueue, criticalThread>>(Unlock(t))
WF_TryLock(t) == WF_<<lock, waitQueue, criticalThread>>(TryLock(t))
WF_Lock(t) == WF_<<lock, waitQueue, criticalThread>>(Lock(t))
Spec == 
  Init 
  /\ □[Next]_<<lock, waitQueue, criticalThread>>
  /\ ∀ t ∈ Threads : (WF_TryLock(t) /\ WF_Lock(t) /\ WF_Unlock(t))
====