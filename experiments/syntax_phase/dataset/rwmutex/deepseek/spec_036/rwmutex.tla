---- MODULE rwmutex ----
EXTENDS TLC, Sequences, Naturals, FiniteSets

CONSTANTS Thread, NullThread

VARIABLES 
    lockState,
    waitQueue,
    threadState,
    activeGuards

(* Bit field constants matching Rust implementation *)
WRITER == 1
UPGRADEABLE_READER == 2
BEING_UPGRADED == 4
READER == 8

(* Lock state decomposition *)
IsWriterSet(lock) == (lock \div WRITER) % 2 = 1
IsUpgradeableReaderSet(lock) == (lock \div UPGRADEABLE_READER) % 2 = 1
IsBeingUpgradedSet(lock) == (lock \div BEING_UPGRADED) % 2 = 1
ReaderCount(lock) == lock \div READER

(* Thread states *)
ThreadState == {"idle", "waiting_read", "waiting_write", "waiting_upread", 
               "holding_read", "holding_write", "holding_upread", "upgrading"}

(* Guard types *)
GuardType == {"read", "write", "upread"}

(* Initialize system *)
Init == 
    /\ lockState = 0
    /\ waitQueue = <<>>
    /\ threadState = [t \in Thread |-> "idle"]
    /\ activeGuards = [type \in GuardType |-> {}]

(* Helper predicates *)
CanAcquireRead(lock) == 
    /\ ~IsWriterSet(lock)
    /\ ~IsBeingUpgradedSet(lock)

CanAcquireWrite(lock) == 
    lock = 0

CanAcquireUpread(lock) == 
    /\ ~IsWriterSet(lock)
    /\ ~IsUpgradeableReaderSet(lock)

CanUpgrade(lock) == 
    /\ IsUpgradeableReaderSet(lock)
    /\ IsBeingUpgradedSet(lock)
    /\ ReaderCount(lock) = 0
    /\ ~IsWriterSet(lock)

(* Atomic state updates *)
AcquireRead(lock) == lock + READER
ReleaseRead(lock) == lock - READER

AcquireWrite(lock) == lock + WRITER
ReleaseWrite(lock) == lock - WRITER

AcquireUpread(lock) == lock + UPGRADEABLE_READER
ReleaseUpread(lock) == lock - UPGRADEABLE_READER

SetBeingUpgraded(lock) == lock + BEING_UPGRADED
ClearBeingUpgraded(lock) == lock - BEING_UPGRADED

(* Wait queue operations *)
Enqueue(queue, thread, op) == Append(queue, [thread |-> thread, op |-> op])
Dequeue(queue) == IF queue /= <<>> THEN SubSeq(queue, 2, Len(queue)) ELSE <<>>
Head(queue) == IF queue /= <<>> THEN queue[1] ELSE [thread |-> NullThread, op |-> "none"]

(* Wake strategies *)
WakeOne(queue) == 
    IF queue /= <<>> THEN
        LET head == Head(queue)
        IN Dequeue(queue)
    ELSE queue

WakeAll(queue) == <<>>

(* Action: Try to acquire read lock *)
TryRead(t) ==
    /\ threadState[t] = "idle"
    /\ LET newLock == AcquireRead(lockState)
       IN IF CanAcquireRead(lockState)
          THEN /\ lockState' = newLock
               /\ threadState' = [threadState EXCEPT ![t] = "holding_read"]
               /\ activeGuards' = [activeGuards EXCEPT !["read"] = activeGuards["read"] \union {t}]
               /\ waitQueue' = waitQueue
               /\ UNCHANGED <<>>
          ELSE /\ lockState' = lockState
               /\ threadState' = [threadState EXCEPT ![t] = "waiting_read"]
               /\ waitQueue' = Enqueue(waitQueue, t, "read")
               /\ activeGuards' = activeGuards
               /\ UNCHANGED <<>>

(* Action: Try to acquire write lock *)
TryWrite(t) ==
    /\ threadState[t] = "idle"
    /\ IF CanAcquireWrite(lockState)
       THEN /\ lockState' = AcquireWrite(lockState)
            /\ threadState' = [threadState EXCEPT ![t] = "holding_write"]
            /\ activeGuards' = [activeGuards EXCEPT !["write"] = activeGuards["write"] \union {t}]
            /\ waitQueue' = waitQueue
            /\ UNCHANGED <<>>
       ELSE /\ threadState' = [threadState EXCEPT ![t] = "waiting_write"]
            /\ waitQueue' = Enqueue(waitQueue, t, "write")
            /\ lockState' = lockState
            /\ activeGuards' = activeGuards
            /\ UNCHANGED <<>>

(* Action: Try to acquire upgradeable read lock *)
TryUpread(t) ==
    /\ threadState[t] = "idle"
    /\ LET newLock == AcquireUpread(lockState)
       IN IF CanAcquireUpread(lockState)
          THEN /\ lockState' = newLock
               /\ threadState' = [threadState EXCEPT ![t] = "holding_upread"]
               /\ activeGuards' = [activeGuards EXCEPT !["upread"] = activeGuards["upread"] \union {t}]
               /\ waitQueue' = waitQueue
               /\ UNCHANGED <<>>
          ELSE /\ lockState' = lockState
               /\ threadState' = [threadState EXCEPT ![t] = "waiting_upread"]
               /\ waitQueue' = Enqueue(waitQueue, t, "upread")
               /\ activeGuards' = activeGuards
               /\ UNCHANGED <<>>

(* Action: Release read guard *)
ReleaseReadGuard(t) ==
    /\ threadState[t] = "holding_read"
    /\ LET newLock == ReleaseRead(lockState)
       IN /\ lockState' = newLock
          /\ threadState' = [threadState EXCEPT ![t] = "idle"]
          /\ activeGuards' = [activeGuards EXCEPT !["read"] = activeGuards["read"] \ {t}]
          /\ waitQueue' = IF ReaderCount(lockState) = 1 THEN WakeOne(waitQueue) ELSE waitQueue
          /\ UNCHANGED <<>>

(* Action: Release write guard *)
ReleaseWriteGuard(t) ==
    /\ threadState[t] = "holding_write"
    /\ lockState' = ReleaseWrite(lockState)
    /\ threadState' = [threadState EXCEPT ![t] = "idle"]
    /\ activeGuards' = [activeGuards EXCEPT !["write"] = activeGuards["write"] \ {t}]
    /\ waitQueue' = WakeAll(waitQueue)
    /\ UNCHANGED <<>>

(* Action: Release upgradeable read guard *)
ReleaseUpreadGuard(t) ==
    /\ threadState[t] = "holding_upread"
    /\ LET newLock == ReleaseUpread(lockState)
       IN /\ lockState' = newLock
          /\ threadState' = [threadState EXCEPT ![t] = "idle"]
          /\ activeGuards' = [activeGuards EXCEPT !["upread"] = activeGuards["upread"] \ {t}]
          /\ waitQueue' = IF lockState = UPGRADEABLE_READER THEN WakeAll(waitQueue) ELSE waitQueue
          /\ UNCHANGED <<>>

(* Action: Upgrade from upread to write *)
Upgrade(t) ==
    /\ threadState[t] = "holding_upread"
    /\ threadState' = [threadState EXCEPT ![t] = "upgrading"]
    /\ lockState' = SetBeingUpgraded(lockState)
    /\ waitQueue' = waitQueue
    /\ activeGuards' = activeGuards
    /\ UNCHANGED <<>>

(* Action: Complete upgrade *)
CompleteUpgrade(t) ==
    /\ threadState[t] = "upgrading"
    /\ IF CanUpgrade(lockState)
       THEN /\ lockState' = AcquireWrite(ClearBeingUpgraded(lockState))
            /\ threadState' = [threadState EXCEPT ![t] = "holding_write"]
            /\ activeGuards' = [activeGuards EXCEPT 
                !["upread"] = activeGuards["upread"] \ {t},
                !["write"] = activeGuards["write"] \union {t}]
       ELSE /\ lockState' = lockState
            /\ threadState' = [threadState EXCEPT ![t] = "holding_upread"]
            /\ activeGuards' = activeGuards
    /\ waitQueue' = waitQueue
    /\ UNCHANGED <<>>

(* Action: Downgrade from write to upread *)
Downgrade(t) ==
    /\ threadState[t] = "holding_write"
    /\ lockState' = AcquireUpread(ReleaseWrite(lockState))
    /\ threadState' = [threadState EXCEPT ![t] = "holding_upread"]
    /\ activeGuards' = [activeGuards EXCEPT 
        !["write"] = activeGuards["write"] \ {t},
        !["upread"] = activeGuards["upread"] \union {t}]
    /\ waitQueue' = waitQueue
    /\ UNCHANGED <<>>

(* Action: Process wait queue *)
ProcessWaitQueue ==
    /\ waitQueue /= <<>>
    /\ LET head == Head(waitQueue)
       IN CASE head.op = "read" -> TryRead(head.thread)
          [] head.op = "write" -> TryWrite(head.thread)
          [] head.op = "upread" -> TryUpread(head.thread)
    /\ waitQueue' = Dequeue(waitQueue)
    /\ UNCHANGED <<lockState, threadState, activeGuards>>

(* Next state relation *)
Next ==
    \/ \E t \in Thread: TryRead(t)
    \/ \E t \in Thread: TryWrite(t)
    \/ \E t \in Thread: TryUpread(t)
    \/ \E t \in Thread: ReleaseReadGuard(t)
    \/ \E t \in Thread: ReleaseWriteGuard(t)
    \/ \E t \in Thread: ReleaseUpreadGuard(t)
    \/ \E t \in Thread: Upgrade(t)
    \/ \E t \in Thread: CompleteUpgrade(t)
    \/ \E t \in Thread: Downgrade(t)
    \/ ProcessWaitQueue

(* Type correctness invariant *)
TypeOK ==
    /\ lockState \in Nat
    /\ waitQueue \in Seq([thread: Thread \cup {NullThread}, op: {"read", "write", "upread", "none"}])
    /\ threadState \in [Thread -> ThreadState]
    /\ activeGuards \in [GuardType -> SUBSET Thread]

(* Specification with fairness *)
Vars == <<lockState, waitQueue, threadState, activeGuards>>
Spec == Init /\ [][Next]_Vars /\ WF_Vars(Next)

====