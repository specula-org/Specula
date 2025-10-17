---- MODULE rwmutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Threads, MaxThreads

VARIABLES lock_state, queue, active_readers, active_writer, active_upreader, upgrading

(* Type definitions *)
ReaderCount == 0..MaxThreads
LockBits == {0, 1}  (* 0: clear, 1: set *)

(* Lock state encoding *)
WRITER_BIT == 1
UPGRADEABLE_READER_BIT == 2  
BEING_UPGRADED_BIT == 4

(* Lock state representation *)
LockState == [writer : LockBits, upreader : LockBits, being_upgraded : LockBits, reader_count : ReaderCount]

(* Queue operations *)
Queue == Seq([type : {"read", "write", "upread"}, thread : Threads])

(* Initial state *)
Init == 
    /\ lock_state = [writer |-> 0, upreader |-> 0, being_upgraded |-> 0, reader_count |-> 0]
    /\ queue = <<>>
    /\ active_readers = {}
    /\ active_writer = {}
    /\ active_upreader = {}
    /\ upgrading = {}

(* Helper predicates *)
CanAcquireRead(lock) ==
    /\ lock.writer = 0
    /\ lock.being_upgraded = 0

CanAcquireWrite(lock) ==
    /\ lock.writer = 0
    /\ lock.upreader = 0  
    /\ lock.reader_count = 0

CanAcquireUpread(lock) ==
    /\ lock.writer = 0
    /\ lock.upreader = 0

CanUpgrade(lock) ==
    /\ lock.upreader = 1
    /\ lock.being_upgraded = 1
    /\ lock.reader_count = 0

CanDowngrade(lock) ==
    /\ lock.writer = 1
    /\ lock.upreader = 0
    /\ lock.being_upgraded = 0
    /\ lock.reader_count = 0

(* Lock state transitions *)
AcquireRead(lock) ==
    [lock EXCEPT !reader_count = lock.reader_count + 1]

ReleaseRead(lock) ==
    [lock EXCEPT !reader_count = lock.reader_count - 1]

AcquireWrite(lock) ==
    [lock EXCEPT !writer = 1]

ReleaseWrite(lock) ==
    [lock EXCEPT !writer = 0]

AcquireUpread(lock) ==
    [lock EXCEPT !upreader = 1]

ReleaseUpread(lock) ==
    [lock EXCEPT !upreader = 0]

StartUpgrade(lock) ==
    [lock EXCEPT !being_upgraded = 1]

CompleteUpgrade(lock) ==
    [lock EXCEPT !writer = 1, !upreader = 0, !being_upgraded = 0]

Downgrade(lock) ==
    [lock EXCEPT !writer = 0, !upreader = 1]

(* Queue wake strategies *)
WakeOne(queue) ==
    IF queue /= <<>> THEN
        LET first == Head(queue) IN
        CASE first.type = "read" -> CanAcquireRead(lock_state)
        [] first.type = "write" -> CanAcquireWrite(lock_state)  
        [] first.type = "upread" -> CanAcquireUpread(lock_state)
    ELSE FALSE

WakeAll(queue) ==
    /\ queue /= <<>>
    /\ \E op \in DOMAIN queue : 
        CASE queue[op].type = "read" -> CanAcquireRead(lock_state)
        [] queue[op].type = "write" -> CanAcquireWrite(lock_state)
        [] queue[op].type = "upread" -> CanAcquireUpread(lock_state)

(* Action definitions *)
AcquireReadAction(t) ==
    /\ t \notin active_readers \cup active_writer \cup active_upreader
    /\ CanAcquireRead(lock_state)
    /\ lock_state' = AcquireRead(lock_state)
    /\ active_readers' = active_readers \cup {t}
    /\ UNCHANGED <<queue, active_writer, active_upreader, upgrading>>

AcquireWriteAction(t) ==
    /\ t \notin active_readers \cup active_writer \cup active_upreader  
    /\ CanAcquireWrite(lock_state)
    /\ lock_state' = AcquireWrite(lock_state)
    /\ active_writer' = {t}
    /\ UNCHANGED <<queue, active_readers, active_upreader, upgrading>>

AcquireUpreadAction(t) ==
    /\ t \notin active_readers \cup active_writer \cup active_upreader
    /\ CanAcquireUpread(lock_state)
    /\ lock_state' = AcquireUpread(lock_state)
    /\ active_upreader' = {t}
    /\ UNCHANGED <<queue, active_readers, active_writer, upgrading>>

EnqueueReadAction(t) ==
    /\ t \notin active_readers \cup active_writer \cup active_upreader
    /\ ~CanAcquireRead(lock_state)
    /\ queue' = Append(queue, [type |-> "read", thread |-> t])
    /\ UNCHANGED <<lock_state, active_readers, active_writer, active_upreader, upgrading>>

EnqueueWriteAction(t) ==
    /\ t \notin active_readers \cup active_writer \cup active_upreader
    /\ ~CanAcquireWrite(lock_state)
    /\ queue' = Append(queue, [type |-> "write", thread |-> t])
    /\ UNCHANGED <<lock_state, active_readers, active_writer, active_upreader, upgrading>>

EnqueueUpreadAction(t) ==
    /\ t \notin active_readers \cup active_writer \cup active_upreader
    /\ ~CanAcquireUpread(lock_state)
    /\ queue' = Append(queue, [type |-> "upread", thread |-> t])
    /\ UNCHANGED <<lock_state, active_readers, active_writer, active_upreader, upgrading>>

ReleaseReadAction(t) ==
    /\ t \in active_readers
    /\ lock_state' = ReleaseRead(lock_state)
    /\ active_readers' = active_readers \ {t}
    /\ IF lock_state'.reader_count = 0 /\ WakeOne(queue) THEN
        LET first_op == Head(queue) IN
        queue' = Tail(queue)
        /\ CASE first_op.type = "read" -> 
               lock_state'' = AcquireRead(lock_state')
               /\ active_readers'' = active_readers' \cup {first_op.thread}
           [] first_op.type = "write" ->
               lock_state'' = AcquireWrite(lock_state')
               /\ active_writer' = {first_op.thread}
           [] first_op.type = "upread" ->
               lock_state'' = AcquireUpread(lock_state')
               /\ active_upreader' = {first_op.thread}
    ELSE
        /\ queue' = queue
        /\ lock_state'' = lock_state'
        /\ UNCHANGED <<active_writer, active_upreader>>
    /\ UNCHANGED <<upgrading>>

ReleaseWriteAction(t) ==
    /\ t \in active_writer
    /\ lock_state' = ReleaseWrite(lock_state)
    /\ active_writer' = {}
    /\ IF WakeAll(queue) THEN
        LET ProcessQueue(ls, q, ar, aw, aur) ==
            IF q = <<>> THEN [ls, q, ar, aw, aur]
            ELSE
                LET op == Head(q) IN
                CASE op.type = "read" -> 
                    IF CanAcquireRead(ls) THEN
                        ProcessQueue(AcquireRead(ls), Tail(q), ar \cup {op.thread}, aw, aur)
                    ELSE [ls, q, ar, aw, aur]
                [] op.type = "write" ->
                    IF CanAcquireWrite(ls) THEN
                        ProcessQueue(AcquireWrite(ls), Tail(q), ar, {op.thread}, aur)
                    ELSE [ls, q, ar, aw, aur]
                [] op.type = "upread" ->
                    IF CanAcquireUpread(ls) THEN
                        ProcessQueue(AcquireUpread(ls), Tail(q), ar, aw, {op.thread})
                    ELSE [ls, q, ar, aw, aur]
        IN
        LET result == ProcessQueue(lock_state', queue, active_readers, active_writer', active_upreader) IN
        lock_state'' = result[1]
        /\ queue' = result[2]
        /\ active_readers' = result[3]
        /\ active_writer'' = result[4]
        /\ active_upreader' = result[5]
    ELSE
        /\ lock_state'' = lock_state'
        /\ queue' = queue
        /\ UNCHANGED <<active_readers, active_upreader>>
    /\ UNCHANGED <<upgrading>>

ReleaseUpreadAction(t) ==
    /\ t \in active_upreader
    /\ lock_state' = ReleaseUpread(lock_state)
    /\ active_upreader' = {}
    /\ IF WakeAll(queue) THEN
        LET ProcessQueue(ls, q, ar, aw, aur) ==
            IF q = <<>> THEN [ls, q, ar, aw, aur]
            ELSE
                LET op == Head(q) IN
                CASE op.type = "read" -> 
                    IF CanAcquireRead(ls) THEN
                        ProcessQueue(AcquireRead(ls), Tail(q), ar \cup {op.thread}, aw, aur)
                    ELSE [ls, q, ar, aw, aur]
                [] op.type = "write" ->
                    IF CanAcquireWrite(ls) THEN
                        ProcessQueue(AcquireWrite(ls), Tail(q), ar, {op.thread}, aur)
                    ELSE [ls, q, ar, aw, aur]
                [] op.type = "upread" ->
                    IF CanAcquireUpread(ls) THEN
                        ProcessQueue(AcquireUpread(ls), Tail(q), ar, aw, {op.thread})
                    ELSE [ls, q, ar, aw, aur]
        IN
        LET result == ProcessQueue(lock_state', queue, active_readers, active_writer, active_upreader') IN
        lock_state'' = result[1]
        /\ queue' = result[2]
        /\ active_readers' = result[3]
        /\ active_writer' = result[4]
        /\ active_upreader'' = result[5]
    ELSE
        /\ lock_state'' = lock_state'
        /\ queue' = queue
        /\ UNCHANGED <<active_readers, active_writer>>
    /\ UNCHANGED <<upgrading>>

StartUpgradeAction(t) ==
    /\ t \in active_upreader
    /\ lock_state.being_upgraded = 0
    /\ lock_state' = StartUpgrade(lock_state)
    /\ upgrading' = upgrading \cup {t}
    /\ UNCHANGED <<queue, active_readers, active_writer, active_upreader>>

CompleteUpgradeAction(t) ==
    /\ t \in active_upreader \cap upgrading
    /\ CanUpgrade(lock_state)
    /\ lock_state' = CompleteUpgrade(lock_state)
    /\ active_upreader' = active_upreader \ {t}
    /\ active_writer' = {t}
    /\ upgrading' = upgrading \ {t}
    /\ UNCHANGED <<queue, active_readers>>

DowngradeAction(t) ==
    /\ t \in active_writer
    /\ CanDowngrade(lock_state)
    /\ lock_state' = Downgrade(lock_state)
    /\ active_writer' = {}
    /\ active_upreader' = {t}
    /\ UNCHANGED <<queue, active_readers, upgrading>>

(* Next state relation *)
Next ==
    \/ \E t \in Threads : AcquireReadAction(t)
    \/ \E t \in Threads : AcquireWriteAction(t)
    \/ \E t \in Threads : AcquireUpreadAction(t)
    \/ \E t \in Threads : EnqueueReadAction(t)
    \/ \E t \in Threads : EnqueueWriteAction(t)
    \/ \E t \in Threads : EnqueueUpreadAction(t)
    \/ \E t \in Threads : ReleaseReadAction(t)
    \/ \E t \in Threads : ReleaseWriteAction(t)
    \/ \E t \in Threads : ReleaseUpreadAction(t)
    \/ \E t \in Threads : StartUpgradeAction(t)
    \/ \E t \in Threads : CompleteUpgradeAction(t)
    \/ \E t \in Threads : DowngradeAction(t)

(* Type correctness *)
TypeOK ==
    /\ lock_state \in LockState
    /\ queue \in Queue
    /\ active_readers \subseteq Threads
    /\ active_writer \subseteq Threads
    /\ active_upreader \subseteq Threads
    /\ upgrading \subseteq Threads
    /\ Cardinality(active_writer) <= 1
    /\ Cardinality(active_upreader) <= 1
    /\ active_readers \cap active_writer = {}
    /\ active_readers \cap active_upreader = {}
    /\ active_writer \cap active_upreader = {}
    /\ LET rc == lock_state.reader_count IN
       rc = Cardinality(active_readers)

(* Specification with fairness *)
vars == <<lock_state, queue, active_readers, active_writer, active_upreader, upgrading>>

Spec == 
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(AcquireReadAction(_))
    /\ WF_vars(AcquireWriteAction(_))
    /\ WF_vars(AcquireUpreadAction(_))
    /\ WF_vars(ReleaseReadAction(_))
    /\ WF_vars(ReleaseWriteAction(_))
    /\ WF_vars(ReleaseUpreadAction(_))
    /\ WF_vars(StartUpgradeAction(_))
    /\ WF_vars(CompleteUpgradeAction(_))
    /\ WF_vars(DowngradeAction(_))

====