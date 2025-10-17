---- MODULE mutex ----

EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Threads

VARIABLES 
    lock,
    waitQueue,
    threadState,
    guardHolder

Vars == <<lock, waitQueue, threadState, guardHolder>>

ThreadStates == {"running", "waiting", "blocked"}

TypeOK == 
    /\ lock \in BOOLEAN
    /\ waitQueue \in Seq(Threads)
    /\ threadState \in [Threads -> ThreadStates]
    /\ guardHolder \in Threads \cup {NULL}

Init ==
    /\ lock = FALSE
    /\ waitQueue = <<>>
    /\ threadState = [t \in Threads |-> "running"]
    /\ guardHolder = NULL

TryLock(t) ==
    /\ threadState[t] = "running"
    /\ guardHolder = NULL
    /\ ~lock
    /\ lock' = TRUE
    /\ guardHolder' = t
    /\ UNCHANGED <<waitQueue, threadState>>

TryLockFail(t) ==
    /\ threadState[t] = "running"
    /\ lock = TRUE
    /\ UNCHANGED <<lock, waitQueue, threadState, guardHolder>>

Lock(t) ==
    /\ threadState[t] = "running"
    /\ guardHolder = NULL
    /\ IF ~lock
       THEN /\ lock' = TRUE
            /\ guardHolder' = t
            /\ UNCHANGED <<waitQueue, threadState>>
       ELSE /\ waitQueue' = Append(waitQueue, t)
            /\ threadState' = [threadState EXCEPT ![t] = "waiting"]
            /\ UNCHANGED <<lock, guardHolder>>

WaitUntilAcquire(t) ==
    /\ threadState[t] = "waiting"
    /\ t \in Range(waitQueue)
    /\ ~lock
    /\ guardHolder = NULL
    /\ Head(waitQueue) = t
    /\ lock' = TRUE
    /\ guardHolder' = t
    /\ waitQueue' = Tail(waitQueue)
    /\ threadState' = [threadState EXCEPT ![t] = "running"]

DropGuard(t) ==
    /\ guardHolder = t
    /\ threadState[t] = "running"
    /\ lock = TRUE
    /\ lock' = FALSE
    /\ guardHolder' = NULL
    /\ IF waitQueue /= <<>>
       THEN /\ LET nextThread == Head(waitQueue)
               IN threadState' = [threadState EXCEPT ![nextThread] = "running"]
            /\ UNCHANGED waitQueue
       ELSE /\ UNCHANGED <<threadState, waitQueue>>

BlockedToWaiting(t) ==
    /\ threadState[t] = "blocked"
    /\ threadState' = [threadState EXCEPT ![t] = "waiting"]
    /\ UNCHANGED <<lock, waitQueue, guardHolder>>

RunningToBlocked(t) ==
    /\ threadState[t] = "running"
    /\ guardHolder /= t
    /\ threadState' = [threadState EXCEPT ![t] = "blocked"]
    /\ UNCHANGED <<lock, waitQueue, guardHolder>>

Next ==
    \E t \in Threads:
        \/ TryLock(t)
        \/ TryLockFail(t)
        \/ Lock(t)
        \/ WaitUntilAcquire(t)
        \/ DropGuard(t)
        \/ BlockedToWaiting(t)
        \/ RunningToBlocked(t)

Spec == 
    /\ Init 
    /\ [][Next]_Vars
    /\ \A t \in Threads: WF_Vars(TryLock(t))
    /\ \A t \in Threads: WF_Vars(Lock(t))
    /\ \A t \in Threads: WF_Vars(WaitUntilAcquire(t))
    /\ \A t \in Threads: WF_Vars(DropGuard(t))
    /\ \A t \in Threads: WF_Vars(BlockedToWaiting(t))

====