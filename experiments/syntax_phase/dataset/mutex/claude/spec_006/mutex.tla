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
    /\ t \in ToSet(waitQueue)
    /\ ~lock
    /\ guardHolder = NULL
    /\ lock' = TRUE
    /\ guardHolder' = t
    /\ waitQueue' = SelectSeq(waitQueue, LAMBDA x: x # t)
    /\ threadState' = [threadState EXCEPT ![t] = "running"]

DropGuard(t) ==
    /\ guardHolder = t
    /\ lock = TRUE
    /\ lock' = FALSE
    /\ guardHolder' = NULL
    /\ IF waitQueue # <<>>
       THEN LET nextThread == Head(waitQueue)
            IN /\ waitQueue' = Tail(waitQueue)
               /\ threadState' = [threadState EXCEPT ![nextThread] = "running"]
       ELSE /\ UNCHANGED <<waitQueue, threadState>>

Next ==
    \E t \in Threads:
        \/ TryLock(t)
        \/ TryLockFail(t)
        \/ Lock(t)
        \/ WaitUntilAcquire(t)
        \/ DropGuard(t)

Spec == Init /\ [][Next]_Vars 
             /\ \A t \in Threads: WF_Vars(TryLock(t))
             /\ \A t \in Threads: WF_Vars(Lock(t))
             /\ \A t \in Threads: WF_Vars(WaitUntilAcquire(t))
             /\ \A t \in Threads: WF_Vars(DropGuard(t))

====