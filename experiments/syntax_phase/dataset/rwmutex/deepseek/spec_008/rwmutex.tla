---- MODULE rwmutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Threads, NullThread

VARIABLES lock, queue, guards, active_thread

(* State representation *)
WriterBit == 1
UpgradeableReaderBit == 2
BeingUpgradedBit == 4
ReaderCountMask == 0..(2^60 - 1)

(* Helper functions *)
IsWriterLocked(state) == state \div WriterBit % 2 = 1
IsUpgradeableReaderLocked(state) == state \div UpgradeableReaderBit % 2 = 1
IsBeingUpgraded(state) == state \div BeingUpgradedBit % 2 = 1
GetReaderCount(state) == state % ReaderCountMask

CanAcquireRead(state) == 
    ~IsWriterLocked(state) /\ ~IsBeingUpgraded(state)

CanAcquireWrite(state) ==
    state = 0

CanAcquireUpread(state) ==
    ~IsWriterLocked(state) /\ ~IsUpgradeableReaderLocked(state)

CanUpgrade(state) ==
    IsUpgradeableReaderLocked(state) /\ IsBeingUpgraded(state) /\ GetReaderCount(state) = 0

CanDowngrade(state) ==
    IsWriterLocked(state) /\ ~IsUpgradeableReaderLocked(state)

(* State transitions *)
AcquireRead(current_state) ==
    LET new_state == current_state + 1
    IN IF CanAcquireRead(current_state) THEN new_state ELSE current_state

ReleaseRead(current_state) ==
    LET new_state == current_state - 1
    IN IF GetReaderCount(current_state) > 0 THEN new_state ELSE current_state

AcquireWrite(current_state) ==
    IF CanAcquireWrite(current_state) THEN WriterBit ELSE current_state

ReleaseWrite(current_state) ==
    IF IsWriterLocked(current_state) THEN 0 ELSE current_state

AcquireUpread(current_state) ==
    IF CanAcquireUpread(current_state) THEN current_state + UpgradeableReaderBit ELSE current_state

ReleaseUpread(current_state) ==
    IF IsUpgradeableReaderLocked(current_state) THEN current_state - UpgradeableReaderBit ELSE current_state

StartUpgrade(current_state) ==
    IF IsUpgradeableReaderLocked(current_state) /\ ~IsBeingUpgraded(current_state) 
    THEN current_state + BeingUpgradedBit ELSE current_state

CompleteUpgrade(current_state) ==
    IF CanUpgrade(current_state)
    THEN WriterBit + UpgradeableReaderBit ELSE current_state

Downgrade(current_state) ==
    IF CanDowngrade(current_state)
    THEN UpgradeableReaderBit ELSE current_state

(* Guard types *)
GuardType == {"read", "write", "upread"}

(* Actions *)
Action == {"acquire_read", "acquire_write", "acquire_upread", 
           "release_read", "release_write", "release_upread",
           "start_upgrade", "complete_upgrade", "downgrade"}

(* Queue operations *)
Enqueue(thread, op, q) == Append(q, <<thread, op>>)
Dequeue(q) == IF q /= <<>> THEN Tail(q) ELSE q
WakeOne(q) == IF q /= <<>> THEN Tail(q) ELSE q
WakeAll(q) == <<>>

(* Process next thread from queue *)
ProcessQueue(current_state, q) ==
    IF q = <<>> THEN current_state
    ELSE
        LET head_op == Head(q)[2]
        IN CASE head_op = "acquire_read" -> 
               IF CanAcquireRead(current_state) THEN AcquireRead(current_state) ELSE current_state
           [] head_op = "acquire_write" ->
               IF CanAcquireWrite(current_state) THEN AcquireWrite(current_state) ELSE current_state
           [] head_op = "acquire_upread" ->
               IF CanAcquireUpread(current_state) THEN AcquireUpread(current_state) ELSE current_state
           [] head_op = "start_upgrade" ->
               StartUpgrade(current_state)
           [] head_op = "complete_upgrade" ->
               CompleteUpgrade(current_state)
           [] head_op = "downgrade" ->
               Downgrade(current_state)
           OTHER -> current_state

(* Main actions *)
AcquireReadAction(thread) ==
    LET can_acquire == CanAcquireRead(lock)
    IN /\ active_thread = thread
       /\ IF can_acquire 
          THEN /\ lock' = AcquireRead(lock)
               /\ guards' = guards \union {[type |-> "read", thread |-> thread]}
               /\ queue' = queue
          ELSE /\ lock' = lock
               /\ guards' = guards
               /\ queue' = Enqueue(thread, "acquire_read", queue)
       /\ active_thread' = NullThread

AcquireWriteAction(thread) ==
    LET can_acquire == CanAcquireWrite(lock)
    IN /\ active_thread = thread
       /\ IF can_acquire 
          THEN /\ lock' = AcquireWrite(lock)
               /\ guards' = guards \union {[type |-> "write", thread |-> thread]}
               /\ queue' = queue
          ELSE /\ lock' = lock
               /\ guards' = guards
               /\ queue' = Enqueue(thread, "acquire_write", queue)
       /\ active_thread' = NullThread

AcquireUpreadAction(thread) ==
    LET can_acquire == CanAcquireUpread(lock)
    IN /\ active_thread = thread
       /\ IF can_acquire 
          THEN /\ lock' = AcquireUpread(lock)
               /\ guards' = guards \union {[type |-> "upread", thread |-> thread]}
               /\ queue' = queue
          ELSE /\ lock' = lock
               /\ guards' = guards
               /\ queue' = Enqueue(thread, "acquire_upread", queue)
       /\ active_thread' = NullThread

ReleaseReadAction(thread) ==
    LET has_guard == \E g \in guards: g.thread = thread /\ g.type = "read"
        new_state == ReleaseRead(lock)
        should_wake == GetReaderCount(lock) = 1
    IN /\ has_guard
       /\ lock' = new_state
       /\ guards' = guards \ {[type |-> "read", thread |-> thread]}
       /\ IF should_wake 
          THEN queue' = WakeOne(queue)
          ELSE queue' = queue
       /\ active_thread' = NullThread

ReleaseWriteAction(thread) ==
    LET has_guard == \E g \in guards: g.thread = thread /\ g.type = "write"
    IN /\ has_guard
       /\ lock' = ReleaseWrite(lock)
       /\ guards' = guards \ {[type |-> "write", thread |-> thread]}
       /\ queue' = WakeAll(queue)
       /\ active_thread' = NullThread

ReleaseUpreadAction(thread) ==
    LET has_guard == \E g \in guards: g.thread = thread /\ g.type = "upread"
        was_only_upreader == IsUpgradeableReaderLocked(lock) /\ ~IsBeingUpgraded(lock)
    IN /\ has_guard
       /\ lock' = ReleaseUpread(lock)
       /\ guards' = guards \ {[type |-> "upread", thread |-> thread]}
       /\ IF was_only_upreader 
          THEN queue' = WakeAll(queue)
          ELSE queue' = queue
       /\ active_thread' = NullThread

StartUpgradeAction(thread) ==
    LET has_guard == \E g \in guards: g.thread = thread /\ g.type = "upread"
    IN /\ has_guard
       /\ active_thread = thread
       /\ lock' = StartUpgrade(lock)
       /\ guards' = guards
       /\ queue' = queue
       /\ active_thread' = NullThread

CompleteUpgradeAction(thread) ==
    LET has_guard == \E g \in guards: g.thread = thread /\ g.type = "upread"
        can_upgrade == CanUpgrade(lock)
    IN /\ has_guard
       /\ active_thread = thread
       /\ IF can_upgrade
          THEN /\ lock' = CompleteUpgrade(lock)
               /\ guards' = (guards \ {[type |-> "upread", thread |-> thread]}) 
                          \union {[type |-> "write", thread |-> thread]}
               /\ queue' = queue
          ELSE /\ lock' = lock
               /\ guards' = guards
               /\ queue' = Enqueue(thread, "complete_upgrade", queue)
       /\ active_thread' = NullThread

DowngradeAction(thread) ==
    LET has_guard == \E g \in guards: g.thread = thread /\ g.type = "write"
    IN /\ has_guard
       /\ active_thread = thread
       /\ lock' = Downgrade(lock)
       /\ guards' = (guards \ {[type |-> "write", thread |-> thread]}) 
                  \union {[type |-> "upread", thread |-> thread]}
       /\ queue' = queue
       /\ active_thread' = NullThread

ThreadAction(thread) ==
    /\ active_thread = NullThread
    /\ active_thread' = thread

(* Next state relation *)
Next ==
    \/ \E thread \in Threads: ThreadAction(thread)
    \/ \E thread \in Threads: AcquireReadAction(thread)
    \/ \E thread \in Threads: AcquireWriteAction(thread)
    \/ \E thread \in Threads: AcquireUpreadAction(thread)
    \/ \E thread \in Threads: ReleaseReadAction(thread)
    \/ \E thread \in Threads: ReleaseWriteAction(thread)
    \/ \E thread \in Threads: ReleaseUpreadAction(thread)
    \/ \E thread \in Threads: StartUpgradeAction(thread)
    \/ \E thread \in Threads: CompleteUpgradeAction(thread)
    \/ \E thread \in Threads: DowngradeAction(thread)

(* Type invariant *)
TypeOK ==
    /\ lock \in Nat
    /\ queue \in Seq(Threads \X Action)
    /\ guards \subseteq (GuardType \X Threads)
    /\ active_thread \in Threads \union {NullThread}
    /\ \A t \in Threads: Cardinality({g \in guards: g.thread = t}) <= 1

(* Initial state *)
Init ==
    /\ lock = 0
    /\ queue = <<>>
    /\ guards = {}
    /\ active_thread = NullThread

(* Fairness conditions *)
vars == <<lock, queue, guards, active_thread>>

Spec == 
    Init /\ [][Next]_vars
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