---- MODULE rwmutex ----
EXTENDS TLC, Sequences, Naturals, FiniteSets

CONSTANTS Threads, NULL

VARIABLES lock_state, queue, held_reads, held_write, held_upread, upgrading_thread

(* Bit field constants matching Rust implementation *)
WRITER == 1 \\cdot (2^62)  (* Bit 63 *)
UPGRADEABLE_READER == 1 \\cdot (2^61)  (* Bit 62 *)
BEING_UPGRADED == 1 \\cdot (2^60)  (* Bit 61 *)
READER_INCREMENT == 1

(* State predicates *)
IsWriterSet(lock) == lock \\div WRITER % 2 = 1
IsUpgradeableReaderSet(lock) == lock \\div UPGRADEABLE_READER % 2 = 1
IsBeingUpgradedSet(lock) == lock \\div BEING_UPGRADED % 2 = 1
GetReaderCount(lock) == lock % BEING_UPGRADED

CanAcquireRead(lock) == 
    ~IsWriterSet(lock) /\ ~IsBeingUpgradedSet(lock)

CanAcquireWrite(lock) == 
    lock = 0

CanAcquireUpgradeableRead(lock) == 
    ~IsWriterSet(lock) /\ ~IsUpgradeableReaderSet(lock)

CanUpgrade(lock) == 
    IsUpgradeableReaderSet(lock) /\ IsBeingUpgradedSet(lock) /\ GetReaderCount(lock) = 0

CanDowngrade(lock) == 
    IsWriterSet(lock) /\ ~IsUpgradeableReaderSet(lock) /\ ~IsBeingUpgradedSet(lock) /\ GetReaderCount(lock) = 0

TypeOK == 
    /\ lock_state \in Nat
    /\ queue \in Seq(Threads \\times ({"read", "write", "upread"}))
    /\ held_reads \in SUBSET Threads
    /\ held_write \in Threads \cup {NULL}
    /\ held_upread \in Threads \cup {NULL}
    /\ upgrading_thread \in Threads \cup {NULL}
    /\ (held_write # NULL) => (held_upread = NULL /\ held_reads = {})
    /\ (held_upread # NULL) => held_write = NULL
    /\ (upgrading_thread # NULL) => (held_upread = upgrading_thread)
    /\ (IsWriterSet(lock_state) <=> (held_write # NULL))
    /\ (IsUpgradeableReaderSet(lock_state) <=> (held_upread # NULL))
    /\ (IsBeingUpgradedSet(lock_state) <=> (upgrading_thread # NULL))
    /\ GetReaderCount(lock_state) = Cardinality(held_reads)

Init == 
    /\ lock_state = 0
    /\ queue = <<>>
    /\ held_reads = {}
    /\ held_write = NULL
    /\ held_upread = NULL
    /\ upgrading_thread = NULL

TryRead(t) == 
    /\ t \notin held_reads
    /\ t \notin {held_write, held_upread}
    /\ CanAcquireRead(lock_state)
    /\ lock_state' = lock_state + READER_INCREMENT
    /\ held_reads' = held_reads \union {t}
    /\ UNCHANGED <<queue, held_write, held_upread, upgrading_thread>>

TryWrite(t) == 
    /\ t \notin held_reads
    /\ t \notin {held_write, held_upread}
    /\ CanAcquireWrite(lock_state)
    /\ lock_state' = lock_state + WRITER
    /\ held_write' = t
    /\ UNCHANGED <<queue, held_reads, held_upread, upgrading_thread>>

TryUpgradeableRead(t) == 
    /\ t \notin held_reads
    /\ t \notin {held_write, held_upread}
    /\ CanAcquireUpgradeableRead(lock_state)
    /\ lock_state' = lock_state + UPGRADEABLE_READER
    /\ held_upread' = t
    /\ UNCHANGED <<queue, held_reads, held_write, upgrading_thread>>

EnqueueOperation(t, op) == 
    /\ queue' = Append(queue, <<t, op>>)
    /\ UNCHANGED <<lock_state, held_reads, held_write, held_upread, upgrading_thread>>

AcquireRead(t) == 
    \/ TryRead(t)
    \/ EnqueueOperation(t, "read")

AcquireWrite(t) == 
    \/ TryWrite(t)
    \/ EnqueueOperation(t, "write")

AcquireUpgradeableRead(t) == 
    \/ TryUpgradeableRead(t)
    \/ EnqueueOperation(t, "upread")

ReleaseRead(t) == 
    /\ t \in held_reads
    /\ held_reads' = held_reads \ {t}
    /\ lock_state' = lock_state - READER_INCREMENT
    /\ IF GetReaderCount(lock_state') = 0 /\ queue # <<>> THEN
        LET head == Head(queue) IN
        LET t2 == head[1] IN
        LET op == head[2] IN
        /\ queue' = Tail(queue)
        /\ CASE op = "read" -> TryRead(t2)
           [] op = "write" -> TryWrite(t2)  
           [] op = "upread" -> TryUpgradeableRead(t2)
       ELSE
        /\ queue' = queue
    /\ UNCHANGED <<held_write, held_upread, upgrading_thread>>

ReleaseWrite(t) == 
    /\ held_write = t
    /\ held_write' = NULL
    /\ lock_state' = lock_state - WRITER
    /\ IF queue # <<>> THEN
        LET head == Head(queue) IN
        LET t2 == head[1] IN
        LET op == head[2] IN
        /\ queue' = Tail(queue)
        /\ CASE op = "read" -> TryRead(t2)
           [] op = "write" -> TryWrite(t2)
           [] op = "upread" -> TryUpgradeableRead(t2)
       ELSE
        /\ queue' = queue
    /\ UNCHANGED <<held_reads, held_upread, upgrading_thread>>

ReleaseUpgradeableRead(t) == 
    /\ held_upread = t
    /\ held_upread' = NULL
    /\ upgrading_thread' = NULL
    /\ lock_state' = lock_state - UPGRADEABLE_READER - (IF IsBeingUpgradedSet(lock_state) THEN BEING_UPGRADED ELSE 0)
    /\ IF queue # <<>> THEN
        LET head == Head(queue) IN
        LET t2 == head[1] IN
        LET op == head[2] IN
        /\ queue' = Tail(queue)
        /\ CASE op = "read" -> TryRead(t2)
           [] op = "write" -> TryWrite(t2)
           [] op = "upread" -> TryUpgradeableRead(t2)
       ELSE
        /\ queue' = queue
    /\ UNCHANGED <<held_reads, held_write>>

StartUpgrade(t) == 
    /\ held_upread = t
    /\ upgrading_thread' = t
    /\ lock_state' = lock_state + BEING_UPGRADED
    /\ UNCHANGED <<queue, held_reads, held_write, held_upread>>

CompleteUpgrade(t) == 
    /\ upgrading_thread = t
    /\ CanUpgrade(lock_state)
    /\ lock_state' = lock_state - UPGRADEABLE_READER - BEING_UPGRADED + WRITER
    /\ held_write' = t
    /\ held_upread' = NULL
    /\ upgrading_thread' = NULL
    /\ UNCHANGED <<queue, held_reads>>

Downgrade(t) == 
    /\ held_write = t
    /\ CanDowngrade(lock_state)
    /\ lock_state' = lock_state - WRITER + UPGRADEABLE_READER
    /\ held_write' = NULL
    /\ held_upread' = t
    /\ UNCHANGED <<queue, held_reads, upgrading_thread>>

Next == 
    \/ \E t \in Threads : AcquireRead(t)
    \/ \E t \in Threads : AcquireWrite(t)
    \/ \E t \in Threads : AcquireUpgradeableRead(t)
    \/ \E t \in Threads : ReleaseRead(t)
    \/ \E t \in Threads : ReleaseWrite(t)
    \/ \E t \in Threads : ReleaseUpgradeableRead(t)
    \/ \E t \in Threads : StartUpgrade(t)
    \/ \E t \in Threads : CompleteUpgrade(t)
    \/ \E t \in Threads : Downgrade(t)

vars == <<lock_state, queue, held_reads, held_write, held_upread, upgrading_thread>>

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

====