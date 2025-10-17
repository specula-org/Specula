---- MODULE mutex ----
EXTENDS TLC, Sequences, Naturals, FiniteSets

CONSTANTS Threads, NULL

VARIABLES lock, waitQueue, threadStates, guardOwner

vars == <<lock, waitQueue, threadStates, guardOwner>>

Init == 
    lock = FALSE /\
    waitQueue = <<>> /\
    threadStates = [t \in Threads |-> "RUNNING"] /\
    guardOwner = NULL

AcquireLock(t) ==
    /\ threadStates[t] = "RUNNING"
    /\ lock = FALSE
    /\ lock' = TRUE
    /\ guardOwner' = t
    /\ threadStates' = [threadStates EXCEPT ![t] = "RUNNING"]
    /\ waitQueue' = waitQueue

TryLock(t) ==
    /\ threadStates[t] = "RUNNING"
    /\ lock = FALSE
    /\ lock' = TRUE
    /\ guardOwner' = t
    /\ threadStates' = [threadStates EXCEPT ![t] = "RUNNING"]
    /\ waitQueue' = waitQueue

BlockThread(t) ==
    /\ threadStates[t] = "RUNNING"
    /\ lock = TRUE
    /\ waitQueue' = Append(waitQueue, t)
    /\ threadStates' = [threadStates EXCEPT ![t] = "WAITING"]
    /\ UNCHANGED <<lock, guardOwner>>

ReleaseLock(t) ==
    /\ threadStates[t] = "RUNNING"
    /\ guardOwner = t
    /\ lock' = FALSE
    /\ guardOwner' = NULL
    /\ IF waitQueue /= <<>> 
        THEN /\ LET nextThread == Head(waitQueue)
             IN
                 waitQueue' = Tail(waitQueue)
                 /\ threadStates' = [threadStates EXCEPT ![nextThread] = "RUNNING"]
        ELSE /\ waitQueue' = waitQueue
             /\ threadStates' = threadStates

WakeThread ==
    /\ waitQueue /= <<>>
    /\ LET nextThread == Head(waitQueue)
       IN
           waitQueue' = Tail(waitQueue)
           /\ threadStates' = [threadStates EXCEPT ![nextThread] = "RUNNING"]
    /\ UNCHANGED <<lock, guardOwner>>

Next == 
    \/ \E t \in Threads: AcquireLock(t)
    \/ \E t \in Threads: TryLock(t)
    \/ \E t \in Threads: BlockThread(t)
    \/ \E t \in Threads: ReleaseLock(t)
    \/ WakeThread

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
====