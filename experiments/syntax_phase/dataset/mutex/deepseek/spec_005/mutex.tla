---- MODULE mutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANT Threads

VARIABLES lockState, waitQueue, threadStates, criticalSection

vars == <<lockState, waitQueue, threadStates, criticalSection>>

ThreadStateType == {"idle", "trying", "waiting", "holding", "releasing"}

Init == 
    /\ lockState = FALSE
    /\ waitQueue = <<>>
    /\ threadStates = [t \in Threads |-> "idle"]
    /\ criticalSection = ""

TypeOK == 
    /\ lockState \in BOOLEAN
    /\ waitQueue \in Seq(Threads)
    /\ threadStates \in [Threads -> ThreadStateType]
    /\ criticalSection \in Threads \cup {""}
    /\ \A t \in Threads: 
        (threadStates[t] = "holding") => (criticalSection = t)
    /\ \A t1, t2 \in Threads: 
        (t1 /= t2) => ~(threadStates[t1] = "holding" /\ threadStates[t2] = "holding")

TryAcquireLock(t) ==
    /\ threadStates[t] = "trying"
    /\ lockState = FALSE
    /\ lockState' = TRUE
    /\ threadStates' = [threadStates EXCEPT ![t] = "holding"]
    /\ criticalSection' = t
    /\ waitQueue' = waitQueue

TryLockFail(t) ==
    /\ threadStates[t] = "trying"
    /\ lockState = TRUE
    /\ threadStates' = [threadStates EXCEPT ![t] = "waiting"]
    /\ waitQueue' = Append(waitQueue, t)
    /\ UNCHANGED <<lockState, criticalSection>>

BlockingLock(t) ==
    /\ threadStates[t] = "idle"
    /\ threadStates' = [threadStates EXCEPT ![t] = "trying"]
    /\ UNCHANGED <<lockState, waitQueue, criticalSection>>

NonBlockingTryLock(t) ==
    /\ threadStates[t] = "idle"
    /\ lockState = FALSE
    /\ lockState' = TRUE
    /\ threadStates' = [threadStates EXCEPT ![t] = "holding"]
    /\ criticalSection' = t
    /\ UNCHANGED <<waitQueue>>

NonBlockingTryLockFail(t) ==
    /\ threadStates[t] = "idle"
    /\ lockState = TRUE
    /\ threadStates' = [threadStates EXCEPT ![t] = "idle"]
    /\ UNCHANGED <<lockState, waitQueue, criticalSection>>

Unlock(t) ==
    /\ threadStates[t] = "holding"
    /\ IF waitQueue = <<>> THEN
        /\ lockState' = FALSE
        /\ criticalSection' = ""
        /\ threadStates' = [threadStates EXCEPT ![t] = "idle"]
        /\ waitQueue' = waitQueue
    ELSE
        /\ LET frontThread == Head(waitQueue) IN
            /\ lockState' = TRUE
            /\ criticalSection' = frontThread
            /\ threadStates' = [threadStates EXCEPT 
                ![t] = "idle",
                ![frontThread] = "holding"]
            /\ waitQueue' = Tail(waitQueue)

ReleaseAndIdle(t) ==
    /\ threadStates[t] = "releasing"
    /\ threadStates' = [threadStates EXCEPT ![t] = "idle"]
    /\ UNCHANGED <<lockState, waitQueue, criticalSection>>

Next == 
    \/ \E t \in Threads: BlockingLock(t)
    \/ \E t \in Threads: NonBlockingTryLock(t)
    \/ \E t \in Threads: NonBlockingTryLockFail(t)
    \/ \E t \in Threads: TryAcquireLock(t)
    \/ \E t \in Threads: TryLockFail(t)
    \/ \E t \in Threads: Unlock(t)
    \/ \E t \in Threads: ReleaseAndIdle(t)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
====