---- MODULE mutex ----
EXTENDS TLC, Sequences, Naturals, FiniteSets
CONSTANTS Threads
null == CHOOSE n : n \notin Threads
VARIABLES lock, waitQueue, csHolder, threadState
vars == <<lock, waitQueue, csHolder, threadState>>
Init == lock = FALSE /\ waitQueue = <<>> /\ csHolder = null /\ threadState = [t \in Threads |-> "idle"]
TypeOK == lock \in BOOLEAN /\ waitQueue \in Seq(Threads) /\ csHolder \in Threads \cup {null} /\ threadState \in [Threads -> {"idle", "waiting", "in_cs"}]
TryLock(t) == /\ threadState[t] # "in_cs" /\ lock = FALSE 
              /\ lock' = TRUE /\ csHolder' = t 
              /\ threadState' = [threadState EXCEPT ![t] = "in_cs"] 
              /\ UNCHANGED waitQueue
Lock(t) == /\ threadState[t] # "in_cs"
           /\ IF lock = FALSE 
              THEN /\ lock' = TRUE /\ csHolder' = t 
                   /\ threadState' = [threadState EXCEPT ![t] = "in_cs"] 
                   /\ UNCHANGED waitQueue
              ELSE /\ waitQueue' = Append(waitQueue, t) 
                   /\ threadState' = [threadState EXCEPT ![t] = "waiting"] 
                   /\ UNCHANGED <<lock, csHolder>>
Unlock(t) == /\ csHolder = t /\ lock = TRUE
             /\ IF waitQueue # <<>> 
                THEN /\ LET u = Head(waitQueue)
                         IN /\ lock' = TRUE 
                            /\ csHolder' = u 
                            /\ waitQueue' = Tail(waitQueue) 
                            /\ threadState' = [threadState EXCEPT ![t] = "idle", ![u] = "in_cs"]
                ELSE /\ lock' = FALSE 
                     /\ csHolder' = null 
                     /\ UNCHANGED waitQueue
                     /\ threadState' = [threadState EXCEPT ![t] = "idle"]
Next == \E t \in Threads : TryLock(t) \/ Lock(t) \/ Unlock(t)
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
====