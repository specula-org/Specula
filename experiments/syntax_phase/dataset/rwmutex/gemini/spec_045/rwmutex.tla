---- MODULE rwmutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Threads
ASSUME IsFiniteSet(Threads) /\ Threads # {}

(***************************************************************************)
(* CONSTANTS AND OPERATORS                                                 *)
(***************************************************************************)
WRITER             == 2^63
UPGRADEABLE_READER == 2^62
BEING_UPGRADED     == 2^61
READER             == 1

ReaderCount(l) == l % BEING_UPGRADED
IsWriter(l) == (l \div WRITER) % 2 = 1
IsUpgradable(l) == (l \div UPGRADEABLE_READER) % 2 = 1
IsUpgrading(l) == (l \div BEING_UPGRADED) % 2 = 1

(***************************************************************************)
(* STATE VARIABLES                                                         *)
(***************************************************************************)
VARIABLES lock, queue, threads

vars == <<lock, queue, threads>>

(***************************************************************************)
(* STATE CONSTRAINTS AND INITIALIZATION                                    *)
(***************************************************************************)
ThreadStates == {"idle", "req_read", "req_write", "req_upread", "wait",
                 "reading", "writing", "upreading",
                 "req_upgrade", "upgrading", "req_downgrade"}

TypeOK ==
    /\ lock \in Nat
    /\ queue \in Seq({<<t, ty>> : t \in Threads, ty \in {"read", "write", "upread"}})
    /\ threads \in [Threads -> [pc: ThreadStates]]

Init ==
    /\ lock = 0
    /\ queue = <<>>
    /\ threads = [t \in Threads |-> [pc |-> "idle"]]

(***************************************************************************)
(* HELPER OPERATORS FOR WAKING THREADS                                     *)
(***************************************************************************)
WokenPc(req_type) ==
    IF req_type = "read" THEN "req_read"
    ELSE IF req_type = "write" THEN "req_write"
    ELSE "req_upread"

RECURSIVE WakeAllThreads(_, _)
WakeAllThreads(q, th) ==
    IF q = <<>> THEN th
    ELSE
        LET woken_thread == Head(q).t
            woken_type   == Head(q).ty
        IN WakeAllThreads(Tail(q), [th EXCEPT ![woken_thread].pc = WokenPc(woken_type)])

(***************************************************************************)
(* ACTIONS                                                                 *)
(***************************************************************************)

(* A thread decides it wants to acquire a lock *)
RequestRead(self) ==
    /\ threads[self].pc = "idle"
    /\ threads' = [threads EXCEPT ![self].pc = "req_read"]
    /\ UNCHANGED <<lock, queue>>

RequestWrite(self) ==
    /\ threads[self].pc = "idle"
    /\ threads' = [threads EXCEPT ![self].pc = "req_write"]
    /\ UNCHANGED <<lock, queue>>

RequestUpread(self) ==
    /\ threads[self].pc = "idle"
    /\ threads' = [threads EXCEPT ![self].pc = "req_upread"]
    /\ UNCHANGED <<lock, queue>>

(* A thread attempts to acquire a read lock. If it fails, it waits. *)
AcquireRead(self) ==
    /\ threads[self].pc = "req_read"
    /\ IF ~IsWriter(lock) /\ ~IsUpgrading(lock)
       THEN (* Success *)
            /\ lock' = lock + READER
            /\ threads' = [threads EXCEPT ![self].pc = "reading"]
            /\ UNCHANGED <<queue>>
       ELSE (* Failure, go to wait queue *)
            /\ queue' = Append(queue, <<t |-> self, ty |-> "read">>)
            /\ threads' = [threads EXCEPT ![self].pc = "wait"]
            /\ UNCHANGED <<lock>>

(* A thread attempts to acquire a write lock. If it fails, it waits. *)
AcquireWrite(self) ==
    /\ threads[self].pc = "req_write"
    /\ IF lock = 0
       THEN (* Success *)
            /\ lock' = WRITER
            /\ threads' = [threads EXCEPT ![self].pc = "writing"]
            /\ UNCHANGED <<queue>>
       ELSE (* Failure, go to wait queue *)
            /\ queue' = Append(queue, <<t |-> self, ty |-> "write">>)
            /\ threads' = [threads EXCEPT ![self].pc = "wait"]
            /\ UNCHANGED <<lock>>

(* A thread attempts to acquire an upgradeable read lock. If it fails, it waits. *)
AcquireUpread(self) ==
    /\ threads[self].pc = "req_upread"
    /\ IF ~IsWriter(lock) /\ ~IsUpgradable(lock)
       THEN (* Success *)
            /\ lock' = lock + UPGRADEABLE_READER
            /\ threads' = [threads EXCEPT ![self].pc = "upreading"]
            /\ UNCHANGED <<queue>>
       ELSE (* Failure, go to wait queue *)
            /\ queue' = Append(queue, <<t |-> self, ty |-> "upread">>)
            /\ threads' = [threads EXCEPT ![self].pc = "wait"]
            /\ UNCHANGED <<lock>>

(* A thread releases its read lock. If it's the last reader, wake one waiter. *)
ReleaseRead(self) ==
    /\ threads[self].pc = "reading"
    /\ lock' = lock - READER
    /\ IF lock' % UPGRADEABLE_READER = 0 /\ queue /= <<>>
       THEN (* Last reader, wake one *)
            LET woken_thread == Head(queue).t
                woken_type   == Head(queue).ty
            IN /\ queue' = Tail(queue)
               /\ threads' = [threads EXCEPT ![self].pc = "idle",
                                             ![woken_thread].pc = WokenPc(woken_type)]
       ELSE (* Not last reader or no waiters *)
            /\ threads' = [threads EXCEPT ![self].pc = "idle"]
            /\ UNCHANGED <<queue>>

(* A thread releases its write lock. Wake all waiters. *)
ReleaseWrite(self) ==
    /\ threads[self].pc = "writing"
    /\ lock' = lock - WRITER
    /\ queue' = <<>>
    /\ threads' = [WakeAllThreads(queue, threads) EXCEPT ![self].pc = "idle"]

(* A thread releases its upgradeable read lock. If it's the only lock holder, wake all. *)
ReleaseUpread(self) ==
    /\ threads[self].pc = "upreading"
    /\ lock' = lock - UPGRADEABLE_READER
    /\ IF lock = UPGRADEABLE_READER
       THEN (* Was the only lock holder, wake all *)
            /\ queue' = <<>>
            /\ threads' = [WakeAllThreads(queue, threads) EXCEPT ![self].pc = "idle"]
       ELSE (* Other readers exist *)
            /\ threads' = [threads EXCEPT ![self].pc = "idle"]
            /\ UNCHANGED <<queue>>

(* An upgradeable reader decides to upgrade. *)
RequestUpgrade(self) ==
    /\ threads[self].pc = "upreading"
    /\ threads' = [threads EXCEPT ![self].pc = "req_upgrade"]
    /\ UNCHANGED <<lock, queue>>

(* The upgrade process begins, blocking new readers. *)
StartUpgrade(self) ==
    /\ threads[self].pc = "req_upgrade"
    /\ lock' = lock + BEING_UPGRADED
    /\ threads' = [threads EXCEPT ![self].pc = "upgrading"]
    /\ UNCHANGED <<queue>>

(* The upgrade completes when all other readers have released their locks. *)
CompleteUpgrade(self) ==
    /\ threads[self].pc = "upgrading"
    /\ lock = UPGRADEABLE_READER + BEING_UPGRADED (* Condition: no other readers *)
    /\ lock' = WRITER
    /\ threads' = [threads EXCEPT ![self].pc = "writing"]
    /\ UNCHANGED <<queue>>

(* A writer decides to downgrade to an upgradeable reader. *)
RequestDowngrade(self) ==
    /\ threads[self].pc = "writing"
    /\ threads' = [threads EXCEPT ![self].pc = "req_downgrade"]
    /\ UNCHANGED <<lock, queue>>

(* The downgrade completes. This is atomic and always succeeds. *)
CompleteDowngrade(self) ==
    /\ threads[self].pc = "req_downgrade"
    /\ lock = WRITER
    /\ lock' = UPGRADEABLE_READER
    /\ threads' = [threads EXCEPT ![self].pc = "upreading"]
    /\ UNCHANGED <<queue>>

(***************************************************************************)
(* NEXT-STATE RELATION AND SPECIFICATION                                   *)
(***************************************************************************)
ThreadAction(self) ==
    \/ RequestRead(self)
    \/ RequestWrite(self)
    \/ RequestUpread(self)
    \/ AcquireRead(self)
    \/ AcquireWrite(self)
    \/ AcquireUpread(self)
    \/ ReleaseRead(self)
    \/ ReleaseWrite(self)
    \/ ReleaseUpread(self)
    \/ RequestUpgrade(self)
    \/ StartUpgrade(self)
    \/ CompleteUpgrade(self)
    \/ RequestDowngrade(self)
    \/ CompleteDowngrade(self)

Next == \E self \in Threads: ThreadAction(self)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

====
