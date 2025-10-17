---- MODULE mutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags
CONSTANTS Thread, NULL
VARIABLES lockState, waitQueue, currentOwner, threadState
vars == <<lockState, waitQueue, currentOwner, threadState>>
TypeOK == 
  ∧ lockState ∈ BOOLEAN
  ∧ waitQueue ∈ Seq(Thread)
  ∧ currentOwner ∈ Thread ∪ {NULL}
  ∧ threadState ∈ [Thread → {"ready", "waiting", "critical"}]
Init == 
  ∧ lockState = FALSE
  ∧ waitQueue = << >>
  ∧ currentOwner = NULL
  ∧ ∀ t ∈ Thread : threadState[t] = "ready"
Lock(t) == 
  ∧ threadState[t] = "ready"
  ∧ IF lockState = FALSE
      THEN ∧ lockState' = TRUE
           ∧ currentOwner' = t
           ∧ threadState' = [threadState EXCEPT ![t] = "critical"]
           ∧ waitQueue' = waitQueue
      ELSE ∧ lockState' = lockState
           ∧ currentOwner' = currentOwner
           ∧ threadState' = [threadState EXCEPT ![t] = "waiting"]
           ∧ waitQueue' = Append(waitQueue, t)
TryLock(t) == 
  ∧ threadState[t] = "ready"
  ∧ IF lockState = FALSE
      THEN ∧ lockState' = TRUE
           ∧ currentOwner' = t
           ∧ threadState' = [threadState EXCEPT ![t] = "critical"]
           ∧ waitQueue' = waitQueue
      ELSE ∧ UNCHANGED <<lockState, currentOwner, threadState, waitQueue>>
Unlock(t) == 
  ∧ threadState[t] = "critical"
  ∧ currentOwner = t
  ∧ IF waitQueue = << >>
      THEN ∧ lockState' = FALSE
           ∧ currentOwner' = NULL
           ∧ waitQueue' = waitQueue
           ∧ threadState' = [threadState EXCEPT ![t] = "ready"]
      ELSE ∧ LET first == Head(waitQueue)
           IN ∧ lockState' = TRUE
              ∧ currentOwner' = first
              ∧ waitQueue' = Tail(waitQueue)
              ∧ threadState' = [threadState EXCEPT ![t] = "ready", ![first] = "critical"]
LockAction == ∃ t ∈ Thread : Lock(t)
TryLockAction == ∃ t ∈ Thread : TryLock(t)
UnlockAction == ∃ t ∈ Thread : Unlock(t)
Next == LockAction ∨ TryLockAction ∨ UnlockAction
Spec == Init ∧ [][Next]_vars ∧ WF_vars(Next)
====