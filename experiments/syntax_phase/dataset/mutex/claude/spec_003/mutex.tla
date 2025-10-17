---- MODULE mutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Threads, NULL

VARIABLES 
    lock,
    waitQueue,
    threadStates,
    guards,
    lockHolder

vars == <<lock, waitQueue, threadStates, guards, lockHolder>>

ThreadState == {"Running", "Waiting"}

TypeOK == 
    /\ lock \in BOOLEAN
    /\ waitQueue \in Seq(Threads)
    /\ threadStates \in [Threads -> ThreadState]
    /\ guards \subseteq Threads
    /\ lockHolder \in Threads \cup {NULL}

Init == 
    /\ lock = FALSE
    /\ waitQueue = <<>>
    /\ threadStates = [t \in Threads |-> "Running"]
    /\ guards = {}
    /\ lockHolder = NULL

CAS(thread, expected, new) ==
    /\ threadStates[thread] = "Running"
    /\ IF lock = expected
       THEN /\ lock' = new
            /\ IF new = TRUE
               THEN lockHolder' = thread
               ELSE lockHolder' = NULL
            /\ UNCHANGED <<waitQueue, threadStates, guards>>
       ELSE UNCHANGED vars

AcquireLock(thread) ==
    CAS(thread, FALSE, TRUE)

ReleaseLock(thread) ==
    /\ threadStates[thread] = "Running"
    /\ lockHolder = thread
    /\ lock' = FALSE
    /\ lockHolder' = NULL
    /\ UNCHANGED <<waitQueue, threadStates, guards>>

WaitUntil(thread) ==
    /\ threadStates[thread] = "Running"
    /\ lock = TRUE
    /\ threadStates' = [threadStates EXCEPT ![thread] = "Waiting"]
    /\ waitQueue' = Append(waitQueue, thread)
    /\ UNCHANGED <<lock, guards, lockHolder>>

WakeOne ==
    /\ waitQueue # <<>>
    /\ LET wokenThread == Head(waitQueue)
       IN /\ threadStates' = [threadStates EXCEPT ![wokenThread] = "Running"]
          /\ waitQueue' = Tail(waitQueue)
    /\ UNCHANGED <<lock, guards, lockHolder>>

CreateGuard(thread) ==
    /\ threadStates[thread] = "Running"
    /\ lockHolder = thread
    /\ thread \notin guards
    /\ guards' = guards \cup {thread}
    /\ UNCHANGED <<lock, waitQueue, threadStates, lockHolder>>

DropGuard(thread) ==
    /\ thread \in guards
    /\ guards' = guards \ {thread}
    /\ ReleaseLock(thread)
    /\ WakeOne
    /\ UNCHANGED threadStates

TryLock(thread) ==
    /\ threadStates[thread] = "Running"
    /\ IF lock = FALSE
       THEN /\ AcquireLock(thread)
            /\ CreateGuard(thread)
       ELSE UNCHANGED vars

Lock(thread) ==
    /\ threadStates[thread] = "Running"
    /\ IF lock = FALSE
       THEN /\ AcquireLock(thread)
            /\ CreateGuard(thread)
       ELSE /\ WaitUntil(thread)
            /\ UNCHANGED <<lock, guards, lockHolder>>

Unlock(thread) ==
    /\ thread \in guards
    /\ DropGuard(thread)

Next == 
    \/ \E thread \in Threads : TryLock(thread)
    \/ \E thread \in Threads : Lock(thread)
    \/ \E thread \in Threads : Unlock(thread)
    \/ \E thread \in Threads : CreateGuard(thread)
    \/ \E thread \in Threads : DropGuard(thread)
    \/ WakeOne

Spec == Init /\ [][Next]_vars /\ WF_vars(WakeOne) /\ \A t \in Threads : WF_vars(Lock(t)) /\ \A t \in Threads : WF_vars(Unlock(t))

====