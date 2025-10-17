---- MODULE rwmutex ----
EXTENDS Naturals, Sequences, FiniteSets
CONSTANT Threads
VARIABLES state, waitQueue, activeThreads
StateType == [writer: BOOLEAN, upreader: BOOLEAN, upgrading: BOOLEAN, readers: Nat]
WaitQueueType == [thread: Threads, op: {"read", "write", "upread"}]
vars == <<state, waitQueue, activeThreads>>
TypeOK == 
    /\ state \in StateType
    /\ waitQueue \in Seq(WaitQueueType)
    /\ activeThreads \subseteq Threads
Init ==
    /\ state = [writer |-> FALSE, upreader |-> FALSE, upgrading |-> FALSE, readers |-> 0]
    /\ waitQueue = <<>>
    /\ activeThreads = {}
CanAcquireRead(s) == s["writer"] = FALSE /\ s["upreader"] = FALSE /\ s["upgrading"] = FALSE
CanAcquireWrite(s) == s["readers"] = 0 /\ s["writer"] = FALSE /\ s["upreader"] = FALSE /\ s["upgrading"] = FALSE
CanAcquireUpRead(s) == s["writer"] = FALSE /\ s["upreader"] = FALSE /\ s["upgrading"] = FALSE
ReadAcquire(t) ==
    /\ t \notin activeThreads
    /\ IF CanAcquireRead(state)
        THEN /\ state' = [state EXCEPT !["readers"] = state["readers"] + 1]
             /\ activeThreads' = activeThreads \cup {t}
             /\ waitQueue' = waitQueue
        ELSE /\ waitQueue' = Append(waitQueue, [thread |-> t, op |-> "read"])
             /\ UNCHANGED <<state, activeThreads>>
WriteAcquire(t) ==
    /\ t \notin activeThreads
    /\ IF CanAcquireWrite(state)
        THEN /\ state' = [state EXCEPT !["writer"] = TRUE]
             /\ activeThreads' = activeThreads \cup {t}
             /\ waitQueue' = waitQueue
        ELSE /\ waitQueue' = Append(waitQueue, [thread |-> t, op |-> "write"])
             /\ UNCHANGED <<state, activeThreads>>
UpReadAcquire(t) ==
    /\ t \notin activeThreads
    /\ IF CanAcquireUpRead(state)
        THEN /\ state' = [state EXCEPT !["upreader"] = TRUE]
             /\ activeThreads' = activeThreads \cup {t}
             /\ waitQueue' = waitQueue
        ELSE /\ waitQueue' = Append(waitQueue, [thread |-> t, op |-> "upread"])
             /\ UNCHANGED <<state, activeThreads>>
Upgrade(t) ==
    /\ t \in activeThreads
    /\ state["upreader"] = TRUE
    /\ state' = [writer |-> FALSE, upreader |-> FALSE, upgrading |-> TRUE, readers |-> state["readers"]]
    /\ UNCHANGED <<waitQueue, activeThreads>>
CompleteUpgrade ==
    /\ state["upgrading"] = TRUE
    /\ state["readers"] = 0
    /\ state' = [writer |-> TRUE, upreader |-> FALSE, upgrading |-> FALSE, readers |-> 0]
    /\ UNCHANGED <<waitQueue, activeThreads>>
Downgrade(t) ==
    /\ t \in activeThreads
    /\ state["writer"] = TRUE
    /\ state' = [writer |-> FALSE, upreader |-> TRUE, upgrading |-> FALSE, readers |-> 0]
    /\ UNCHANGED <<waitQueue, activeThreads>>
ReleaseRead(t) ==
    /\ t \in activeThreads
    /\ state["readers"] > 0
    /\ LET newState == [state EXCEPT !["readers"] = state["readers"] - 1] IN
       LET newActiveThreads == activeThreads \ {t} IN
       IF state["readers"] = 1
       THEN IF \E i \in DOMAIN waitQueue: waitQueue[i]["op"] = "read" /\ CanAcquireRead(newState)
            THEN LET firstIndex == CHOOSE i \in DOMAIN waitQueue: waitQueue[i]["op"] = "read" /\ CanAcquireRead(newState) /\ \A j \in 1..(i-1) : ~ (waitQueue[j]["op"] = "read" /\ CanAcquireRead(newState)) IN
                 LET elem == waitQueue[firstIndex] IN
                 /\ state' = [newState EXCEPT !["readers"] = newState["readers"] + 1]
                 /\ activeThreads' = newActiveThreads \cup {elem["thread"]}
                 /\ waitQueue' = SubSeq(waitQueue, 1, firstIndex-1) \o SubSeq(waitQueue, firstIndex+1, Len(waitQueue))
            ELSE /\ state' = newState
                 /\ activeThreads' = newActiveThreads
                 /\ UNCHANGED waitQueue
       ELSE /\ state' = newState
            /\ activeThreads' = newActiveThreads
            /\ UNCHANGED waitQueue
ReleaseWrite(t) ==
    /\ t \in activeThreads
    /\ state["writer"] = TRUE
    /\ LET newState == [state EXCEPT !["writer"] = FALSE] IN
       LET newActiveThreads == activeThreads \ {t} IN
       IF \E i \in DOMAIN waitQueue: (LET elem == waitQueue[i] IN (elem["op"] = "write" /\ CanAcquireWrite(newState)) \/ (elem["op"] = "upread" /\ CanAcquireUpRead(newState)))
       THEN LET firstIndex == CHOOSE i \in DOMAIN waitQueue: (LET elem == waitQueue[i] IN (elem["op"] = "write" /\ CanAcquireWrite(newState)) \/ (elem["op"] = "upread" /\ CanAcquireUpRead(newState))) /\ \A j \in 1..(i-1) : (LET elemJ == waitQueue[j] IN ~((elemJ["op"] = "write" /\ CanAcquireWrite(newState)) \/ (elemJ["op"] = "upread" /\ CanAcquireUpRead(newState)))) IN
            LET elem == waitQueue[firstIndex] IN
            /\ IF elem["op"] = "write"
               THEN /\ state' = [newState EXCEPT !["writer"] = TRUE]
                    /\ activeThreads' = newActiveThreads \cup {elem["thread"]}
               ELSE /\ state' = [newState EXCEPT !["upreader"] = TRUE]
                    /\ activeThreads' = newActiveThreads \cup {elem["thread"]}
            /\ waitQueue' = SubSeq(waitQueue, 1, firstIndex-1) \o SubSeq(waitQueue, firstIndex+1, Len(waitQueue))
       ELSE /\ state' = newState
            /\ activeThreads' = newActiveThreads
            /\ UNCHANGED waitQueue
ReleaseUpRead(t) ==
    /\ t \in activeThreads
    /\ state["upreader"] = TRUE
    /\ LET newState == [state EXCEPT !["upreader"] = FALSE] IN
       LET newActiveThreads == activeThreads \ {t} IN
       IF \E i \in DOMAIN waitQueue: (LET elem == waitQueue[i] IN (elem["op"] = "write" /\ CanAcquireWrite(newState)) \/ (elem["op"] = "upread" /\ CanAcquireUpRead(newState)))
       THEN LET firstIndex == CHOOSE i \in DOMAIN waitQueue: (LET elem == waitQueue[i] IN (elem["op"] = "write" /\ CanAcquireWrite(newState)) \/ (elem["op"] = "upread" /\ CanAcquireUpRead(newState))) /\ \A j \in 1..(i-1) : (LET elemJ == waitQueue[j] IN ~((elemJ["op"] = "write" /\ CanAcquireWrite(newState)) \/ (elemJ["op"] = "upread" /\ CanAcquireUpRead(newState)))) IN
            LET elem == waitQueue[firstIndex] IN
            /\ IF elem["op"] = "write"
               THEN /\ state' = [newState EXCEPT !["writer"] = TRUE]
                    /\ activeThreads' = newActiveThreads \cup {elem["thread"]}
               ELSE /\ state' = [newState EXCEPT !["upreader"] = TRUE]
                    /\ activeThreads' = newActiveThreads \cup {elem["thread"]}
            /\ waitQueue' = SubSeq(waitQueue, 1, firstIndex-1) \o SubSeq(waitQueue, firstIndex+1, Len(waitQueue))
       ELSE /\ state' = newState
            /\ activeThreads' = newActiveThreads
            /\ UNCHANGED waitQueue
Next ==
    \/ \E t \in Threads: ReadAcquire(t)
    \/ \E t \in Threads: WriteAcquire(t)
    \/ \E t \in Threads: UpReadAcquire(t)
    \/ \E t \in Threads: Upgrade(t)
    \/ CompleteUpgrade
    \/ \E t \in Threads: Downgrade(t)
    \/ \E t \in Threads: ReleaseRead(t)
    \/ \E t \in Threads: ReleaseWrite(t)
    \/ \E t \in Threads: ReleaseUpRead(t)
Spec == Init /\ [][Next]_vars
====