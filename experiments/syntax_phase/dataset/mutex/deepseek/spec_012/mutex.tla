---- MODULE mutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags
CONSTANTS Threads, NULL
ASSUME Threads ≠ {} ∧ NULL ∉ Threads
VARIABLES lock, waitQueue, csOwner
TypeOK == lock ∈ BOOLEAN ∧ waitQueue ∈ Seq(Threads) ∧ csOwner ∈ Threads ∪ {NULL}
Init == lock = FALSE ∧ waitQueue = << >> ∧ csOwner = NULL
TryLock(t) == ∧ lock = FALSE
              ∧ lock' = TRUE
              ∧ csOwner' = t
              ∧ waitQueue' = waitQueue
BlockingLock(t) == ∧ lock = TRUE
                   ∧ t ∉ Range(waitQueue)  \* Fix: Changed SeqRange to Range (correct operator from SequencesExt)
                   ∧ waitQueue' = Append(waitQueue, t)
                   ∧ UNCHANGED <<lock, csOwner>>
Unlock(t) == ∧ csOwner = t
             ∧ lock' = FALSE
             ∧ csOwner' = NULL
             ∧ waitQueue' = waitQueue
AcquireFromQueue == ∧ lock = FALSE
                    ∧ waitQueue ≠ << >>
                    ∧ LET first == Head(waitQueue) IN
                      lock' = TRUE
                      ∧ csOwner' = first
                      ∧ waitQueue' = Tail(waitQueue)
Next == ∃ t ∈ Threads : TryLock(t) ∨ BlockingLock(t) ∨ Unlock(t) ∨ AcquireFromQueue
Spec == Init ∧ □[Next]_<<lock, waitQueue, csOwner>> ∧ ∀ t ∈ Threads : WF_<<lock, waitQueue, csOwner>>(Unlock(t)) ∧ WF_<<lock, waitQueue, csOwner>>(AcquireFromQueue)
====