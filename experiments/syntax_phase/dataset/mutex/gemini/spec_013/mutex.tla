---- MODULE mutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Threads, None

VARIABLES locked, lockHolder, waitQueue, pc

vars == <<locked, lockHolder, waitQueue, pc>>

TypeOK ==
    /\ locked \in BOOLEAN
    /\ lockHolder \in Threads \cup {None}
    /\ waitQueue \in Seq(Threads)
    /\ pc \in [Threads -> {"idle", "critical_section", "waiting"}]

Init ==
    /\ locked = FALSE
    /\ lockHolder = None
    /\ waitQueue = <<>>
    /\ pc = [t \in Threads |-> "idle"]

TryToLock(t) ==
    /\ pc[t] = "idle"
    /\ IF \lnot locked THEN
        /\ locked' = TRUE
        /\ lockHolder' = t
        /\ pc' = [pc EXCEPT ![t] = "critical_section"]
        /\ UNCHANGED waitQueue
    /\ ELSE
        \/ /\ pc' = [pc EXCEPT ![t] = "idle"]
           /\ UNCHANGED <<locked, lockHolder, waitQueue>>
        \/ /\ waitQueue' = Append(waitQueue, t)
           /\ pc' = [pc EXCEPT ![t] = "waiting"]
           /\ UNCHANGED <<locked, lockHolder>>

Unlock(t) ==
    /\ pc[t] = "critical_section"
    /\ locked' = FALSE
    /\ lockHolder' = None
    /\ IF Len(waitQueue) > 0 THEN
        LET wokenThread == Head(waitQueue) IN
        /\ waitQueue' = Tail(waitQueue)
        /\ pc' = [pc EXCEPT ![t] = "idle", ![wokenThread] = "idle"]
    /\ ELSE
        /\ waitQueue' = waitQueue
        /\ pc' = [pc EXCEPT ![t] = "idle"]

Next ==
    \E t \in Threads:
        \/ TryToLock(t)
        \/ Unlock(t)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

====