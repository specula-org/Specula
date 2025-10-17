---- MODULE mutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags
CONSTANTS Threads, NULL
ASSUME Threads ≠ {} ∧ NULL ∉ Threads
VARIABLES lock, owner, waitQueue
vars == <<lock, owner, waitQueue>>
Init == 
  ∧ lock = FALSE
  ∧ owner = NULL
  ∧ waitQueue = << >>
TryLock(t) == 
  IF lock = FALSE THEN
    ∧ lock' = TRUE
    ∧ owner' = t
    ∧ waitQueue' = waitQueue
  ELSE
    ∧ UNCHANGED vars
Lock(t) == 
  ∧ t ≠ owner
  ∧ (IF waitQueue = << >> THEN TRUE ELSE t ∉ Range(waitQueue))
  ∧ IF lock = FALSE THEN
      ∧ lock' = TRUE
      ∧ owner' = t
      ∧ waitQueue' = waitQueue
    ELSE
      ∧ waitQueue' = Append(waitQueue, t)
      ∧ UNCHANGED <<lock, owner>>
Unlock(t) == 
  ∧ owner = t
  ∧ lock' = FALSE
  ∧ owner' = NULL
  ∧ IF waitQueue ≠ << >> THEN
      waitQueue' = Tail(waitQueue)
    ELSE
      waitQueue' = waitQueue
Next == 
  ∃ t ∈ Threads : TryLock(t) ∨ Lock(t) ∨ Unlock(t)
Spec == 
  Init 
  ∧ □[Next]_vars
  ∧ ∀ t ∈ Threads : WF_vars(Unlock(t))
====