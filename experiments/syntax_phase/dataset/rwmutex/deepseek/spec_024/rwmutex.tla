---- MODULE rwmutex ----
EXTENDS TLC, Sequences, Naturals, FiniteSets

CONSTANTS Threads, MaxThreads
ASSUME Cardinality(Threads) = MaxThreads

VARIABLES lock, queue, guards, active_threads

(* State encoding *)
WRITER == 1 * (2^63)
UPGRADEABLE_READER == 1 * (2^62)
BEING_UPGRADED == 1 * (2^61)
READER_COUNT_MASK == (1 * (2^61)) - 1

(* Helper functions *)
IsWriterLocked(state) == state \div WRITER > 0
IsUpgradeableReaderLocked(state) == (state \div UPGRADEABLE_READER) % 2 > 0
IsBeingUpgraded(state) == (state \div BEING_UPGRADED) % 2 > 0
GetReaderCount(state) == state % READER_COUNT_MASK

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

(* Type invariant *)
TypeOK == 
    /\ lock \in Nat
    /\ queue \in Seq(Threads)
    /\ guards \in [Threads -> {"none", "read", "write", "upread"}]
    /\ active_threads \in SUBSET Threads
    /\ \A t \in Threads: guards[t] \in {"none", "read", "write", "upread"}

(* Initial state *)
Init == 
    /\ lock = 0
    /\ queue = <<>>
    /\ guards = [t \in Threads |-> "none"]
    /\ active_threads = {}

(* Action definitions *)
TryRead(t) ==
    /\ guards[t] = "none"
    /\ ~(t \in active_threads)
    /\ LET new_state == lock + 1
    IN  IF CanAcquireRead(lock)
        THEN /\ lock' = new_state
             /\ guards' = [guards EXCEPT ![t] = "read"]
             /\ active_threads' = active_threads \union {t}
             /\ UNCHANGED queue
        ELSE /\ lock' = lock
             /\ UNCHANGED <<guards, queue, active_threads>>

TryWrite(t) ==
    /\ guards[t] = "none"
    /\ ~(t \in active_threads)
    /\ IF CanAcquireWrite(lock)
       THEN /\ lock' = lock + WRITER
            /\ guards' = [guards EXCEPT ![t] = "write"]
            /\ active_threads' = active_threads \union {t}
            /\ UNCHANGED queue
       ELSE UNCHANGED <<lock, guards, queue, active_threads>>

TryUpread(t) ==
    /\ guards[t] = "none"
    /\ ~(t \in active_threads)
    /\ LET new_state == lock + UPGRADEABLE_READER
    IN  IF CanAcquireUpread(lock)
        THEN /\ lock' = new_state
             /\ guards' = [guards EXCEPT ![t] = "upread"]
             /\ active_threads' = active_threads \union {t}
             /\ UNCHANGED queue
        ELSE /\ lock' = lock
             /\ UNCHANGED <<guards, queue, active_threads>>

Read(t) ==
    \/ TryRead(t)
    \/ /\ ~CanAcquireRead(lock)
       /\ guards[t] = "none"
       /\ ~(t \in active_threads)
       /\ queue' = Append(queue, t)
       /\ UNCHANGED <<lock, guards, active_threads>>

Write(t) ==
    \/ TryWrite(t)
    \/ /\ ~CanAcquireWrite(lock)
       /\ guards[t] = "none"
       /\ ~(t \in active_threads)
       /\ queue' = Append(queue, t)
       /\ UNCHANGED <<lock, guards, active_threads>>

Upread(t) ==
    \/ TryUpread(t)
    \/ /\ ~CanAcquireUpread(lock)
       /\ guards[t] = "none"
       /\ ~(t \in active_threads)
       /\ queue' = Append(queue, t)
       /\ UNCHANGED <<lock, guards, active_threads>>

ReleaseRead(t) ==
    /\ guards[t] = "read"
    /\ t \in active_threads
    /\ LET new_state == lock - 1
       reader_count_after == GetReaderCount(new_state)
    IN  /\ lock' = new_state
        /\ guards' = [guards EXCEPT ![t] = "none"]
        /\ active_threads' = active_threads \ {t}
        /\ IF reader_count_after = 0
           THEN (* wake one waiting thread *)
                /\ IF queue /= <<>>
                   THEN LET head == Head(queue)
                        IN queue' = Tail(queue)
                   ELSE queue' = queue
           ELSE queue' = queue

ReleaseWrite(t) ==
    /\ guards[t] = "write"
    /\ t \in active_threads
    /\ lock' = lock - WRITER
    /\ guards' = [guards EXCEPT ![t] = "none"]
    /\ active_threads' = active_threads \ {t}
    /\ (* wake all waiting threads *)
       queue' = <<>>

ReleaseUpread(t) ==
    /\ guards[t] = "upread"
    /\ t \in active_threads
    /\ LET new_state == lock - UPGRADEABLE_READER
    IN  /\ lock' = new_state
        /\ guards' = [guards EXCEPT ![t] = "none"]
        /\ active_threads' = active_threads \ {t}
        /\ IF IsUpgradeableReaderLocked(lock) /\ ~IsUpgradeableReaderLocked(new_state)
           THEN queue' = <<>>  (* wake all *)
           ELSE queue' = queue

Upgrade(t) ==
    /\ guards[t] = "upread"
    /\ t \in active_threads
    /\ LET upgraded_state == lock + BEING_UPGRADED
    IN  IF CanUpgrade(upgraded_state)
        THEN /\ lock' = (upgraded_state - UPGRADEABLE_READER - BEING_UPGRADED) + WRITER
             /\ guards' = [guards EXCEPT ![t] = "write"]
             /\ UNCHANGED <<queue, active_threads>>
        ELSE /\ lock' = upgraded_state
             /\ UNCHANGED <<guards, queue, active_threads>>

Downgrade(t) ==
    /\ guards[t] = "write"
    /\ t \in active_threads
    /\ IF CanDowngrade(lock)
       THEN /\ lock' = (lock - WRITER) + UPGRADEABLE_READER
            /\ guards' = [guards EXCEPT ![t] = "upread"]
            /\ UNCHANGED <<queue, active_threads>>
       ELSE UNCHANGED <<lock, guards, queue, active_threads>>

(* Next state relation *)
Next == 
    \/ \E t \in Threads: Read(t)
    \/ \E t \in Threads: Write(t)
    \/ \E t \in Threads: Upread(t)
    \/ \E t \in Threads: ReleaseRead(t)
    \/ \E t \in Threads: ReleaseWrite(t)
    \/ \E t \in Threads: ReleaseUpread(t)
    \/ \E t \in Threads: Upgrade(t)
    \/ \E t \in Threads: Downgrade(t)

(* Specification with fairness *)
Vars == <<lock, queue, guards, active_threads>>
Spec == 
    Init /\ [][Next]_Vars
    /\ WF_Vars(Next)
====