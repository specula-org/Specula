---- MODULE mutex ----
EXTENDS TLC, Sequences, Naturals, FiniteSets
CONSTANT Threads, NULL
ASSUME NULL \notin Threads
ThreadSet == Threads \cup {NULL}
VARIABLES holder, queue
TypeOK == holder \in ThreadSet /\ queue \in Seq(Threads) /\ (holder = NULL \/ holder \in Threads)
Init == holder = NULL /\ queue = << >>
TryLock(t) == /\ t \in Threads
              /\ holder = NULL
              /\ holder' = t
              /\ queue' = queue
Lock(t) == /\ t \in Threads
           /\ holder \in Threads
           /\ holder \neq t
           /\ t \notin Range(queue)
           /\ queue' = Append(queue, t)
           /\ holder' = holder
Unlock(t) == /\ t \in Threads
             /\ holder = t
             /\ IF queue \neq << >>
                 THEN /\ holder' = Head(queue)
                      /\ queue' = Tail(queue)
                 ELSE /\ holder' = NULL
                      /\ queue' = queue
Next == \E t \in Threads : TryLock(t) \/ Lock(t) \/ Unlock(t)
Spec == Init /\ [][Next]_<<holder, queue>> /\ \A t \in Threads : WF_<<holder, queue>>(Unlock(t))
====