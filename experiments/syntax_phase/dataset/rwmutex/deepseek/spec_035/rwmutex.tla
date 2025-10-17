---- MODULE rwmutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Thread, NullThread

VARIABLES 
    lockState,
    waitQueue,
    threadState,
    activeGuards

(* Bit field constants matching Rust implementation *)
WRITER == 1 << 63
UPGRADEABLE_READER == 1 << 62
BEING_UPGRADED == 1 << 61
READER == 1

(* Lock state decomposition *)
IsWriterSet(lock) == (lock \div WRITER) % 2 = 1
IsUpgradeableReaderSet(lock) == (lock \div UPGRADEABLE_READER) % 2 = 1
IsBeingUpgradedSet(lock) == (lock \div BEING_UPGRADED) % 2 = 1
ReaderCount(lock) == lock % (1 << 61)

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
               /\ activeGuards' = [activeGuards EXCEPT !["read"] = activeGuards["read"] \cup {t}]
               /\ waitQueue' = waitQueue
          ELSE /\ lockState' = ReleaseRead(newLock)
               /\ threadState' = [threadState EXCEPT ![t] = "waiting_read"]
               /\ waitQueue' = Enqueue(waitQueue, t, "read")
               /\ activeGuards' = activeGuards

(* Action: Try to acquire write lock *)
TryWrite(t) ==
    /\ threadState[t] = "idle"
    /\ IF CanAcquireWrite(lockState)
       THEN /\ lockState' = AcquireWrite(lockState)
            /\ threadState' = [threadState EXCEPT ![t] = "holding_write"]
            /\ activeGuards' = [activeGuards EXCEPT !["write"] = activeGuards["write"] \cup {t}]
            /\ waitQueue' = waitQueue
       ELSE /\ threadState' = [threadState EXCEPT ![t] = "waiting_write"]
            /\ waitQueue' = Enqueue(waitQueue, t, "write")
            /\ lockState' = lockState
            /\ activeGuards' = activeGuards

(* Action: Try to acquire upgradeable read lock *)
TryUpread(t) ==
    /\ threadState[t] = "idle"
    /\ LET newLock == AcquireUpread(lockState)
       IN IF CanAcquireUpread(lockState)
          THEN /\ lockState' = newLock
               /\ threadState' = [threadState EXCEPT ![t] = "holding_upread"]
               /\ activeGuards' = [activeGuards EXCEPT !["upread"] = activeGuards["upread"] \cup {t}]
               /\ waitQueue' = waitQueue
          ELSE /\ lockState' = IF IsWriterSet(lockState) THEN ReleaseUpread(newLock) ELSE newLock
               /\ threadState' = [threadState EXCEPT ![t] = "waiting_upread"]
               /\ waitQueue' = Enqueue(waitQueue, t, "upread")
               /\ activeGuards' = activeGuards

(* Action: Release read guard *)
ReleaseReadGuard(t) ==
    /\ threadState[t] = "holding_read"
    /\ LET newLock == ReleaseRead(lockState)
       IN /\ lockState' = newLock
          /\ threadState' = [threadState EXCEPT ![t] = "idle"]
          /\ activeGuards' = [activeGuards EXCEPT !["read"] = activeGuards["read"] \ {t}]
          /\ waitQueue' = IF ReaderCount(lockState) = READER THEN WakeOne(waitQueue) ELSE waitQueue

(* Action: Release write guard *)
ReleaseWriteGuard(t) ==
    /\ threadState[t] = "holding_write"
    /\ lockState' = ReleaseWrite(lockState)
    /\ threadState' = [threadState EXCEPT ![t] = "idle"]
    /\ activeGuards' = [activeGuards EXCEPT !["write"] = activeGuards["write"] \ {t}]
    /\ waitQueue' = WakeAll(waitQueue)

(* Action: Release upgradeable read guard *)
ReleaseUpreadGuard(t) ==
    /\ threadState[t] = "holding_upread"
    /\ LET newLock == ReleaseUpread(lockState)
       IN /\ lockState' = newLock
          /\ threadState' = [threadState EXCEPT ![t] = "idle"]
          /\ activeGuards' = [activeGuards EXCEPT !["upread"] = activeGuards["upread"] \ {t}]
          /\ waitQueue' = IF lockState = UPGRADEABLE_READER THEN WakeAll(waitQueue) ELSE waitQueue

(* Action: Upgrade from upread to write *)
Upgrade(t) ==
    /\ threadState[t] = "holding_upread"
    /\ threadState' = [threadState EXCEPT ![t] = "upgrading"]
    /\ lockState' = SetBeingUpgraded(lockState)
    /\ waitQueue' = waitQueue
    /\ activeGuards' = activeGuards

(* Action: Complete upgrade *)
CompleteUpgrade(t) ==
    /\ threadState[t] = "upgrading"
    /\ IF CanUpgrade(lockState)
       THEN /\ lockState' = AcquireWrite(ClearBeingUpgraded(lockState))
            /\ threadState' = [threadState EXCEPT ![t] = "holding_write"]
            /\ activeGuards' = [activeGuards EXCEPT 
                !["upread"] = activeGuards["upread"] \ {t},
                !["write"] = activeGuards["write"] \cup {t}]
       ELSE /\ lockState' = lockState
            /\ threadState' = [threadState EXCEPT ![t] = "holding_upread"]
    /\ waitQueue' = waitQueue

(* Action: Downgrade from write to upread *)
Downgrade(t) ==
    /\ threadState[t] = "holding_write"
    /\ lockState' = AcquireUpread(ReleaseWrite(lockState))
    /\ threadState' = [threadState EXCEPT ![t] = "holding_upread"]
    /\ activeGuards' = [activeGuards EXCEPT 
        !["write"] = activeGuards["write"] \ {t},
        !["upread"] = activeGuards["upread"] \cup {t}]
    /\ waitQueue' = waitQueue

(* Action: Process wait queue *)
ProcessWaitQueue ==
    /\ waitQueue /= <<>>
    /\ LET head == Head(waitQueue)
       IN CASE head.op = "read" -> TryRead(head.thread)
          [] head.op = "write" -> TryWrite(head.thread)
          [] head.op = "upread" -> TryUpread(head.thread)
    /\ waitQueue' = Dequeue(waitQueue)

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
    /\ lockState \in 0..(WRITER + UPGRADEABLE_READER + BEING_UPGRADED + (1 << 61) - 1)
    /\ waitQueue \in Seq([thread: Thread \cup {NullThread}, op: {"read", "write", "upread", "none"}])
    /\ threadState \in [Thread -> ThreadState]
    /\ activeGuards \in [GuardType -> SUBSET Thread]

(* Specification with fairness *)
Vars == <<lockState, waitQueue, threadState, activeGuards>>
Spec == Init /\ [][Next]_Vars 
          /\ WF_Vars(TryRead(_))
          /\ WF_Vars(TryWrite(_)) 
          /\ WF_Vars(TryUpread(_))
          /\ WF_Vars(ReleaseReadGuard(_))
          /\ WF_Vars(ReleaseWriteGuard(_))
          /\ WF_Vars(ReleaseUpreadGuard(_))
          /\ WF_Vars(Upgrade(_))
          /\ WF_Vars(CompleteUpgrade(_))
          /\ WF_Vars(Downgrade(_))
          /\ WF_Vars(ProcessWaitQueue)

====