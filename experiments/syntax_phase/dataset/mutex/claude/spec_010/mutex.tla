---- MODULE mutex ----

EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Threads

VARIABLES 
    lock,
    waitQueue,
    threadState,
    guardOwner

Vars == <<lock, waitQueue, threadState, guardOwner>>

ThreadStates == {"running", "waiting", "blocked"}

TypeOK ==
    /\ lock \in BOOLEAN
    /\ waitQueue \in Seq(Threads)
    /\ threadState \in [Threads -> ThreadStates]
    /\ guardOwner \in Threads \cup {NULL}

Init ==
    /\ lock = FALSE
    /\ waitQueue = <<>>
    /\ threadState = [t \in Threads |-> "running"]
    /\ guardOwner = NULL

TryLock(t) ==
    /\ threadState[t] = "running"
    /\ guardOwner = NULL
    /\ ~lock
    /\ lock' = TRUE
    /\ guardOwner' = t
    /\ UNCHANGED <<waitQueue, threadState>>

TryLockFail(t) ==
    /\ threadState[t] = "running"
    /\ lock = TRUE
    /\ UNCHANGED <<lock, waitQueue, threadState, guardOwner>>

Lock(t) ==
    /\ threadState[t] = "running"
    /\ guardOwner = NULL
    /\ IF ~lock
       THEN /\ lock' = TRUE
            /\ guardOwner' = t
            /\ UNCHANGED <<waitQueue, threadState>>
       ELSE /\ waitQueue' = Append(waitQueue, t)
            /\ threadState' = [threadState EXCEPT ![t] = "waiting"]
            /\ UNCHANGED <<lock, guardOwner>>

WaitUntilAcquire(t) ==
    /\ threadState[t] = "waiting"
    /\ t \in ToSet(waitQueue)
    /\ ~lock
    /\ guardOwner = NULL
    /\ Head(waitQueue) = t
    /\ lock' = TRUE
    /\ guardOwner' = t
    /\ waitQueue' = Tail(waitQueue)
    /\ threadState' = [threadState EXCEPT ![t] = "running"]

Unlock(t) ==
    /\ threadState[t] = "running"
    /\ guardOwner = t
    /\ lock = TRUE
    /\ lock' = FALSE
    /\ guardOwner' = NULL
    /\ IF waitQueue /= <<>>
       THEN /\ LET nextThread == Head(waitQueue)
               IN threadState' = [threadState EXCEPT ![nextThread] = "blocked"]
            /\ UNCHANGED waitQueue
       ELSE /\ UNCHANGED <<waitQueue, threadState>>

WakeOne ==
    /\ waitQueue /= <<>>
    /\ \E t \in ToSet(waitQueue) : threadState[t] = "blocked"
    /\ LET blockedThread == CHOOSE t \in ToSet(waitQueue) : threadState[t] = "blocked"
       IN threadState' = [threadState EXCEPT ![blockedThread] = "waiting"]
    /\ UNCHANGED <<lock, waitQueue, guardOwner>>

GuardDrop(t) ==
    /\ threadState[t] = "running"
    /\ guardOwner = t
    /\ lock = TRUE
    /\ lock' = FALSE
    /\ guardOwner' = NULL
    /\ IF waitQueue /= <<>>
       THEN /\ LET nextThread == Head(waitQueue)
               IN threadState' = [threadState EXCEPT ![nextThread] = "blocked"]
            /\ UNCHANGED waitQueue
       ELSE /\ UNCHANGED <<waitQueue, threadState>>

Next ==
    \/ \E t \in Threads : TryLock(t)
    \/ \E t \in Threads : TryLockFail(t)
    \/ \E t \in Threads : Lock(t)
    \/ \E t \in Threads : WaitUntilAcquire(t)
    \/ \E t \in Threads : Unlock(t)
    \/ WakeOne
    \/ \E t \in Threads : GuardDrop(t)

Spec == Init /\ [][Next]_Vars 
        /\ \A t \in Threads : WF_Vars(WaitUntilAcquire(t))
        /\ \A t \in Threads : WF_Vars(GuardDrop(t))
        /\ WF_Vars(WakeOne)

====