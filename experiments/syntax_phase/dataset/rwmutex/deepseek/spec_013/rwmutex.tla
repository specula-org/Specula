---- MODULE rwmutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Threads, Data

VARIABLES 
    lockState,      \* AtomicUsize state: [writer: BOOLEAN, upreader: BOOLEAN, being_upgraded: BOOLEAN, readers: Nat]
    waitQueue,      \* Sequence of waiting threads with their operation type
    heldGuards,     \* Set of tuples: <<thread, guardType, guardId>> where guardType ∈ {"read", "write", "upread"}
    nextGuardId,    \* Counter for unique guard identifiers
    dataValue       \* Protected data value

(* Bit field constants matching Rust code *)
WRITER == 1 << (63)  
UPGRADEABLE_READER == 1 << (62)
BEING_UPGRADED == 1 << (61)
READER_INCREMENT == 1

(* Helper functions for state decomposition *)
IsWriterSet(lock) == lock \div WRITER % 2 = 1
IsUpreaderSet(lock) == lock \div UPGRADEABLE_READER % 2 = 1  
IsBeingUpgradedSet(lock) == lock \div BEING_UPGRADED % 2 = 1
ReaderCount(lock) == lock % (1 << 61)

(* State predicates *)
CanAcquireRead(lock) == 
    ~IsWriterSet(lock) & ~IsBeingUpgradedSet(lock)

CanAcquireWrite(lock) == 
    lock = 0  \* No readers, no writer, no upreader

CanAcquireUpread(lock) == 
    ~IsWriterSet(lock) & ~IsUpreaderSet(lock)

CanUpgrade(lock) ==
    IsUpreaderSet(lock) & IsBeingUpgradedSet(lock) & ReaderCount(lock) = 0

(* Operation types for wait queue *)
Ops == {"read", "write", "upread"}

(* Guard types *)
GuardTypes == {"read", "write", "upread"}

(* Initialize variables *)
Init == 
    /\ lockState = 0
    /\ waitQueue = <<>>
    /\ heldGuards = {}
    /\ nextGuardId = 1
    /\ dataValue \in Data

(* TryRead action - non-blocking attempt *)
TryRead(thread) ==
    LET newLock == lockState + READER_INCREMENT
    IN /\ ~(\E guard \in heldGuards: guard[1] = thread)  \* Thread doesn't already hold a guard
       /\ IF CanAcquireRead(lockState)
          THEN /\ lockState' = newLock
               /\ heldGuards' = heldGuards \cup {<<thread, "read", nextGuardId>>}
               /\ nextGuardId' = nextGuardId + 1
               /\ UNCHANGED <<waitQueue, dataValue>>
          ELSE /\ FALSE  \* Failed attempt
               /\ UNCHANGED <<lockState, waitQueue, heldGuards, nextGuardId, dataValue>>

(* TryWrite action - non-blocking attempt *)
TryWrite(thread) ==
    /\ ~(\E guard \in heldGuards: guard[1] = thread)
    /\ IF CanAcquireWrite(lockState)
       THEN /\ lockState' = lockState + WRITER
            /\ heldGuards' = heldGuards \cup {<<thread, "write", nextGuardId>>}
            /\ nextGuardId' = nextGuardId + 1
            /\ UNCHANGED <<waitQueue, dataValue>>
       ELSE /\ FALSE
            /\ UNCHANGED <<lockState, waitQueue, heldGuards, nextGuardId, dataValue>>

(* TryUpread action - non-blocking attempt *)
TryUpread(thread) ==
    /\ ~(\E guard \in heldGuards: guard[1] = thread)
    /\ IF CanAcquireUpread(lockState)
       THEN /\ lockState' = lockState + UPGRADEABLE_READER
            /\ heldGuards' = heldGuards \cup {<<thread, "upread", nextGuardId>>}
            /\ nextGuardId' = nextGuardId + 1
            /\ UNCHANGED <<waitQueue, dataValue>>
       ELSE /\ FALSE
            /\ UNCHANGED <<lockState, waitQueue, heldGuards, nextGuardId, dataValue>>

(* Blocking acquire operations - add to wait queue *)
AcquireRead(thread) ==
    /\ ~(\E guard \in heldGuards: guard[1] = thread)
    /\ waitQueue' = Append(waitQueue, <<thread, "read">>)
    /\ UNCHANGED <<lockState, heldGuards, nextGuardId, dataValue>>

AcquireWrite(thread) ==
    /\ ~(\E guard \in heldGuards: guard[1] = thread)
    /\ waitQueue' = Append(waitQueue, <<thread, "write">>)
    /\ UNCHANGED <<lockState, heldGuards, nextGuardId, dataValue>>

AcquireUpread(thread) ==
    /\ ~(\E guard \in heldGuards: guard[1] = thread)
    /\ waitQueue' = Append(waitQueue, <<thread, "upread">>)
    /\ UNCHANGED <<lockState, heldGuards, nextGuardId, dataValue>>

(* Wait queue processing - try to satisfy waiting threads *)
ProcessWaitQueue ==
    LET canProcess ==
        IF waitQueue /= <<>> 
        THEN LET head == Head(waitQueue)
             IN CASE head[2] = "read" -> CanAcquireRead(lockState)
                 [] head[2] = "write" -> CanAcquireWrite(lockState)  
                 [] head[2] = "upread" -> CanAcquireUpread(lockState)
        ELSE FALSE
    IN
    IF canProcess
    THEN LET head == Head(waitQueue)
             thread == head[1]
             op == head[2]
         IN CASE op = "read" -> 
                /\ lockState' = lockState + READER_INCREMENT
                /\ heldGuards' = heldGuards \cup {<<thread, "read", nextGuardId>>}
                /\ nextGuardId' = nextGuardId + 1
             [] op = "write" ->
                /\ lockState' = lockState + WRITER  
                /\ heldGuards' = heldGuards \cup {<<thread, "write", nextGuardId>>}
                /\ nextGuardId' = nextGuardId + 1
             [] op = "upread" ->
                /\ lockState' = lockState + UPGRADEABLE_READER
                /\ heldGuards' = heldGuards \cup {<<thread, "upread", nextGuardId>>}
                /\ nextGuardId' = nextGuardId + 1
         /\ waitQueue' = Tail(waitQueue)
         /\ UNCHANGED dataValue
    ELSE UNCHANGED <<lockState, waitQueue, heldGuards, nextGuardId, dataValue>>

(* Release operations *)
ReleaseRead(thread, guardId) ==
    LET guard == <<thread, "read", guardId>>
    IN /\ guard \in heldGuards
       /\ LET newLock == lockState - READER_INCREMENT
          IN /\ lockState' = newLock
             /\ heldGuards' = heldGuards \ {guard}
             /\ IF ReaderCount(newLock) = 0  \* Last reader - wake one
                THEN /\ IF waitQueue /= <<>>
                       THEN waitQueue' = Tail(waitQueue)  \* wake_one semantics
                       ELSE waitQueue' = waitQueue
                ELSE waitQueue' = waitQueue
             /\ UNCHANGED <<nextGuardId, dataValue>>

ReleaseWrite(thread, guardId) ==
    LET guard == <<thread, "write", guardId>>
    IN /\ guard \in heldGuards
       /\ lockState' = lockState - WRITER
       /\ heldGuards' = heldGuards \ {guard}
       /\ waitQueue' = <<>>  \* wake_all semantics - all threads retry
       /\ UNCHANGED <<nextGuardId, dataValue>>

ReleaseUpread(thread, guardId) ==
    LET guard == <<thread, "upread", guardId>>
    IN /\ guard \in heldGuards
       /\ LET newLock == lockState - UPGRADEABLE_READER
          IN /\ lockState' = newLock
             /\ heldGuards' = heldGuards \ {guard}
             /\ IF newLock = 0  \* Was the only upreader - wake all
                THEN waitQueue' = <<>>
                ELSE waitQueue' = waitQueue
             /\ UNCHANGED <<nextGuardId, dataValue>>

(* Upgrade operation *)
StartUpgrade(thread, guardId) ==
    LET upreadGuard == <<thread, "upread", guardId>>
    IN /\ upreadGuard \in heldGuards
       /\ ~IsBeingUpgradedSet(lockState)
       /\ lockState' = lockState + BEING_UPGRADED
       /\ UNCHANGED <<waitQueue, heldGuards, nextGuardId, dataValue>>

CompleteUpgrade(thread, guardId) ==
    LET upreadGuard == <<thread, "upread", guardId>>
    IN /\ upreadGuard \in heldGuards
       /\ IsBeingUpgradedSet(lockState)
       /\ CanUpgrade(lockState)
       /\ lockState' = (lockState - UPGRADEABLE_READER - BEING_UPGRADED) + WRITER
       /\ heldGuards' = (heldGuards \ {upreadGuard}) \cup {<<thread, "write", nextGuardId>>}
       /\ nextGuardId' = nextGuardId + 1
       /\ UNCHANGED <<waitQueue, dataValue>>

(* Downgrade operation *)
Downgrade(thread, guardId) ==
    LET writeGuard == <<thread, "write", guardId>>
    IN /\ writeGuard \in heldGuards
       /\ lockState' = (lockState - WRITER) + UPGRADEABLE_READER
       /\ heldGuards' = (heldGuards \ {writeGuard}) \cup {<<thread, "upread", nextGuardId>>}
       /\ nextGuardId' = nextGuardId + 1
       /\ UNCHANGED <<waitQueue, dataValue>>

(* Data access operations *)
ReadData(thread, guardId) ==
    LET guard == <<thread, "read", guardId>>
    IN /\ guard \in heldGuards
       /\ UNCHANGED <<lockState, waitQueue, heldGuards, nextGuardId, dataValue>>

WriteData(thread, guardId, newVal) ==
    LET guard == <<thread, "write", guardId>>
    IN /\ guard \in heldGuards
       /\ dataValue' = newVal
       /\ UNCHANGED <<lockState, waitQueue, heldGuards, nextGuardId>>

(* Type invariant *)
TypeOK ==
    /\ lockState \in Nat
    /\ waitQueue \in Seq(Threads \times Ops)
    /\ heldGuards \subseteq (Threads \times GuardTypes \times Nat)
    /\ nextGuardId \in Nat
    /\ dataValue \in Data
    /\ \A <<t1, ty1, id1>>, <<t2, ty2, id2>> \in heldGuards: 
         (t1 = t2) => (id1 = id2)  \* Each thread holds at most one guard

(* Next-state relation *)
Next ==
    \/ \E thread \in Threads: TryRead(thread)
    \/ \E thread \in Threads: TryWrite(thread) 
    \/ \E thread \in Threads: TryUpread(thread)
    \/ \E thread \in Threads: AcquireRead(thread)
    \/ \E thread \in Threads: AcquireWrite(thread)
    \/ \E thread \in Threads: AcquireUpread(thread)
    \/ ProcessWaitQueue
    \/ \E thread \in Threads, guardId \in Nat: ReleaseRead(thread, guardId)
    \/ \E thread \in Threads, guardId \in Nat: ReleaseWrite(thread, guardId)
    \/ \E thread \in Threads, guardId \in Nat: ReleaseUpread(thread, guardId)
    \/ \E thread \in Threads, guardId \in Nat: StartUpgrade(thread, guardId)
    \/ \E thread \in Threads, guardId \in Nat: CompleteUpgrade(thread, guardId)
    \/ \E thread \in Threads, guardId \in Nat: Downgrade(thread, guardId)
    \/ \E thread \in Threads, guardId \in Nat: ReadData(thread, guardId)
    \/ \E thread \in Threads, guardId \in Nat, newVal \in Data: WriteData(thread, guardId, newVal)

(* Fairness specification *)
Spec == 
    /\ Init
    /\ [][Next]_<<lockState, waitQueue, heldGuards, nextGuardId, dataValue>>
    /\ WF_<<lockState, waitQueue, heldGuards, nextGuardId, dataValue>>(Next)

====