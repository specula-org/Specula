---- MODULE mutex ----
EXTENDS TLC, Sequences, Naturals, FiniteSets
CONSTANTS Threads
VARIABLES lock, waitQueue, holder
null == CHOOSE n : n \notin Threads
TypeOK == /\ lock \in BOOLEAN
          /\ waitQueue \in Seq(Threads)
          /\ holder \in Threads \cup {null}
Init == /\ lock = FALSE
        /\ waitQueue = <<>>
        /\ holder = null
Acquire(t) == /\ t \in Threads
              /\ holder /= t
              /\ IF lock = FALSE
                 THEN /\ lock' = TRUE
                      /\ holder' = t
                      /\ waitQueue' = waitQueue
                 ELSE /\ ~(t \in Range(waitQueue))
                      /\ lock' = lock
                      /\ holder' = holder
                      /\ waitQueue' = Append(waitQueue, t)
TryAcquire(t) == /\ t \in Threads
                 /\ holder /= t
                 /\ IF lock = FALSE
                    THEN /\ lock' = TRUE
                         /\ holder' = t
                         /\ waitQueue' = waitQueue
                    ELSE /\ UNCHANGED <<lock, holder, waitQueue>>
Release(t) == /\ t \in Threads
              /\ holder = t
              /\ IF waitQueue /= <<>>
                 THEN /\ LET w == Head(waitQueue) IN
                       /\ lock' = TRUE
                       /\ holder' = w
                       /\ waitQueue' = Tail(waitQueue)
                 ELSE /\ lock' = FALSE
                      /\ holder' = null
                      /\ waitQueue' = waitQueue
Next == \E t \in Threads : Acquire(t) \/ TryAcquire(t) \/ Release(t)
Spec == Init /\ [][Next]_<<lock, waitQueue, holder>> /\ WF_<<lock, waitQueue, holder>>(Next)
====