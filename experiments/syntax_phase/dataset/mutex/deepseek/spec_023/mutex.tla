---- MODULE mutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANT Threads
CONSTANT MaxThreads

VARIABLES lockState, waitQueue, threadStates, criticalSection

vars == <<lockState, waitQueue, threadStates, criticalSection>>

ThreadStateType == {"idle", "trying", "waiting", "critical"}

TypeOK == 
    /\ lockState \in BOOLEAN
    /\ waitQueue \in Seq(Threads)
    /\ threadStates \in [Threads -> ThreadStateType]
    /\ criticalSection \in SUBSET Threads
    /\ Cardinality(criticalSection) \leq 1
    /\ \A t \in Threads: 
        (threadStates[t] = "critical") <=> (t \in criticalSection)

Init == 
    /\ lockState = FALSE
    /\ waitQueue = <<>>
    /\ threadStates = [t \in Threads |-> "idle"]
    /\ criticalSection = {}

AcquireLock(t) ==
    /\ threadStates[t] = "trying"
    /\ lockState = FALSE
    /\ lockState' = TRUE
    /\ threadStates' = [threadStates EXCEPT ![t] = "critical"]
    /\ criticalSection' = {t}
    /\ waitQueue' = waitQueue

TryLockSuccess(t) ==
    /\ threadStates[t] = "idle"
    /\ AcquireLock(t)

TryLockFail(t) ==
    /\ threadStates[t] = "idle"
    /\ lockState = TRUE
    /\ threadStates' = [threadStates EXCEPT ![t] = "idle"]
    /\ UNCHANGED <<lockState, waitQueue, criticalSection>>

BlockOnLock(t) ==
    /\ threadStates[t] = "trying"
    /\ lockState = TRUE
    /\ threadStates' = [threadStates EXCEPT ![t] = "waiting"]
    /\ waitQueue' = Append(waitQueue, t)
    /\ UNCHANGED <<lockState, criticalSection>>

Unlock(t) ==
    /\ threadStates[t] = "critical"
    /\ lockState' = FALSE
    /\ threadStates' = [threadStates EXCEPT ![t] = "idle"]
    /\ criticalSection' = {}
    /\ IF waitQueue /= <<>> 
        THEN 
            LET firstThread == Head(waitQueue)
            IN 
                /\ waitQueue' = Tail(waitQueue)
                /\ threadStates' = [threadStates' EXCEPT ![firstThread] = "trying"]
        ELSE 
            /\ waitQueue' = waitQueue

WakeAndAcquire ==
    /\ lockState = FALSE
    /\ waitQueue /= <<>>
    LET firstThread == Head(waitQueue)
    IN
        /\ waitQueue' = Tail(waitQueue)
        /\ lockState' = TRUE
        /\ threadStates' = [threadStates EXCEPT ![firstThread] = "critical"]
        /\ criticalSection' = {firstThread}

Next ==
    \/ \E t \in Threads: TryLockSuccess(t)
    \/ \E t \in Threads: TryLockFail(t)
    \/ \E t \in Threads: BlockOnLock(t)
    \/ \E t \in Threads: Unlock(t)
    \/ WakeAndAcquire

Spec == 
    /\ Init 
    /\ [][Next]_vars
    /\ WF_vars(Next)

====