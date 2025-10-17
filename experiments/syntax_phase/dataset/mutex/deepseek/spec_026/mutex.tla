---- MODULE mutex ----
EXTENDS Sequences, Naturals, FiniteSets
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
  ∧ t ∉ Range(waitQueue)
  ∧ IF lock = FALSE THEN
      ∧ lock' = TRUE
      ∧ owner' = t
      ∧ waitQueue' = waitQueue
    ELSE
      ∧ waitQueue' = Append(waitQueue, t)
      ∧ UNCHANGED <<lock, owner>>
Unlock(t) == 
  ∧ owner = t
  ∧ IF waitQueue ≠ << >> THEN
      ∧ lock' = TRUE
      ∧ owner' = Head(waitQueue)
      ∧ waitQueue' = Tail(waitQueue)
    ELSE
      ∧ lock' = FALSE
      ∧ owner' = NULL
      ∧ waitQueue' = waitQueue
Next == 
  ∃ t ∈ Threads : TryLock(t) ∨ Lock(t) ∨ Unlock(t)
Spec == 
  Init 
  ∧ □[Next]_vars
  ∧ WF_vars(Next)
====