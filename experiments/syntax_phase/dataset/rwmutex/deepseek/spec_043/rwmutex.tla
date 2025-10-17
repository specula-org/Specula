---- MODULE rwmutex ----
EXTENDS TLC, Sequences, Naturals, FiniteSets

CONSTANTS Threads, MaxReaders
ASSUME MaxReaders \in Nat /\ MaxReaders > 0

VARIABLES lock_state, wait_queue, thread_states, reader_count

(* Bit field constants matching the Rust code *)
WRITER == 2^63
UPGRADEABLE_READER == 2^62
BEING_UPGRADED == 2^61

(* Lock state predicates *)
HasWriter(lock) == (lock \div WRITER) % 2 = 1
HasUpgradeableReader(lock) == (lock \div UPGRADEABLE_READER) % 2 = 1
HasBeingUpgraded(lock) == (lock \div BEING_UPGRADED) % 2 = 1
ReaderCount(lock) == lock % (2^61)

(* Type invariant *)
TypeOK == 
    /\ lock_state \in Nat
    /\ wait_queue \in Seq(Threads)
    /\ thread_states \in [Threads -> {"idle", "reading", "writing", "upreading", "upgrading", "waiting_read", "waiting_write", "waiting_upread"}]
    /\ reader_count \in [Threads -> Nat]
    /\ \A t \in Threads: reader_count[t] <= MaxReaders
    /\ (HasWriter(lock_state) => (\E t \in Threads: thread_states[t] = "writing"))
    /\ (HasUpgradeableReader(lock_state) => (\E t \in Threads: thread_states[t] \in {"upreading", "upgrading"}))
    /\ (HasBeingUpgraded(lock_state) => (\E t \in Threads: thread_states[t] = "upgrading"))
    /\ ReaderCount(lock_state) = Cardinality({t \in Threads: thread_states[t] = "reading"})

(* Initial state *)
Init == 
    /\ lock_state = 0
    /\ wait_queue = <<>>
    /\ thread_states = [t \in Threads |-> "idle"]
    /\ reader_count = [t \in Threads |-> 0]

(* TryRead action - non-blocking attempt *)
TryRead(t) ==
    /\ thread_states[t] = "idle"
    /\ ~HasWriter(lock_state)
    /\ ~HasBeingUpgraded(lock_state)
    /\ ReaderCount(lock_state) < MaxReaders
    /\ lock_state' = lock_state + 1
    /\ thread_states' = [thread_states EXCEPT ![t] = "reading"]
    /\ reader_count' = [reader_count EXCEPT ![t] = reader_count[t] + 1]
    /\ UNCHANGED wait_queue

(* Read action - blocking *)
Read(t) ==
    /\ thread_states[t] = "idle"
    /\ (HasWriter(lock_state) \/ HasBeingUpgraded(lock_state) \/ ReaderCount(lock_state) >= MaxReaders)
    /\ wait_queue' = Append(wait_queue, t)
    /\ thread_states' = [thread_states EXCEPT ![t] = "waiting_read"]
    /\ UNCHANGED <<lock_state, reader_count>>

(* TryWrite action - non-blocking attempt *)
TryWrite(t) ==
    /\ thread_states[t] = "idle"
    /\ lock_state = 0
    /\ lock_state' = WRITER
    /\ thread_states' = [thread_states EXCEPT ![t] = "writing"]
    /\ UNCHANGED <<wait_queue, reader_count>>

(* Write action - blocking *)
Write(t) ==
    /\ thread_states[t] = "idle"
    /\ lock_state # 0
    /\ wait_queue' = Append(wait_queue, t)
    /\ thread_states' = [thread_states EXCEPT ![t] = "waiting_write"]
    /\ UNCHANGED <<lock_state, reader_count>>

(* TryUpread action - non-blocking attempt *)
TryUpread(t) ==
    /\ thread_states[t] = "idle"
    /\ ~HasWriter(lock_state)
    /\ ~HasUpgradeableReader(lock_state)
    /\ lock_state' = lock_state + UPGRADEABLE_READER
    /\ thread_states' = [thread_states EXCEPT ![t] = "upreading"]
    /\ UNCHANGED <<wait_queue, reader_count>>

(* Upread action - blocking *)
Upread(t) ==
    /\ thread_states[t] = "idle"
    /\ (HasWriter(lock_state) \/ HasUpgradeableReader(lock_state))
    /\ wait_queue' = Append(wait_queue, t)
    /\ thread_states' = [thread_states EXCEPT ![t] = "waiting_upread"]
    /\ UNCHANGED <<lock_state, reader_count>>

(* Read release - wake one waiter *)
ReadRelease(t) ==
    /\ thread_states[t] = "reading"
    /\ reader_count[t] > 0
    /\ lock_state' = lock_state - 1
    /\ thread_states' = [thread_states EXCEPT ![t] = "idle"]
    /\ reader_count' = [reader_count EXCEPT ![t] = reader_count[t] - 1]
    /\ \/ /\ wait_queue # <<>>
           /\ LET first == Head(wait_queue)
              IN \/ /\ thread_states[first] = "waiting_write"
                    /\ wait_queue' = Tail(wait_queue)
                    /\ thread_states' = [thread_states' EXCEPT ![first] = "writing"]
                    /\ lock_state' = WRITER
                 \/ /\ thread_states[first] = "waiting_upread"
                    /\ wait_queue' = Tail(wait_queue)
                    /\ thread_states' = [thread_states' EXCEPT ![first] = "upreading"]
                    /\ lock_state' = lock_state' + UPGRADEABLE_READER
                 \/ /\ thread_states[first] = "waiting_read"
                    /\ wait_queue' = Tail(wait_queue)
                    /\ thread_states' = [thread_states' EXCEPT ![first] = "reading"]
                    /\ reader_count' = [reader_count' EXCEPT ![first] = reader_count'[first] + 1]
                    /\ lock_state' = lock_state' + 1
       \/ /\ wait_queue = <<>>
           /\ UNCHANGED wait_queue

(* Write release - wake all waiters *)
WriteRelease(t) ==
    /\ thread_states[t] = "writing"
    /\ lock_state' = lock_state - WRITER
    /\ thread_states' = [thread_states EXCEPT ![t] = "idle"]
    /\ LET new_queue == <<>>
        new_thread_states == thread_states'
        new_lock_state == lock_state'
        new_reader_count == reader_count
        IN IF wait_queue # <<>>
           THEN LET ProcessWaiters(queue, t_states, l_state, r_count) ==
                    IF queue = <<>> THEN <<t_states, l_state, queue, r_count>>
                    ELSE LET first == Head(queue)
                         rest == Tail(queue)
                         IN IF t_states[first] = "waiting_write"
                            THEN ProcessWaiters(rest, [t_states EXCEPT ![first] = "writing"], WRITER, r_count)
                            ELSE IF t_states[first] = "waiting_upread"
                                 THEN ProcessWaiters(rest, [t_states EXCEPT ![first] = "upreading"], l_state + UPGRADEABLE_READER, r_count)
                                 ELSE IF t_states[first] = "waiting_read"
                                      THEN ProcessWaiters(rest, [t_states EXCEPT ![first] = "reading"], l_state + 1, [r_count EXCEPT ![first] = r_count[first] + 1])
                                      ELSE ProcessWaiters(rest, t_states, l_state, r_count)
                result == ProcessWaiters(wait_queue, new_thread_states, new_lock_state, new_reader_count)
            IN /\ thread_states' = result[1]
               /\ lock_state' = result[2]
               /\ wait_queue' = result[3]
               /\ reader_count' = result[4]
           ELSE /\ UNCHANGED <<wait_queue, reader_count>>

(* Upgradeable reader release - wake all waiters *)
UpreadRelease(t) ==
    /\ thread_states[t] = "upreading"
    /\ lock_state' = lock_state - UPGRADEABLE_READER
    /\ thread_states' = [thread_states EXCEPT ![t] = "idle"]
    /\ LET new_queue == <<>>
        new_thread_states == thread_states'
        new_lock_state == lock_state'
        new_reader_count == reader_count
        IN IF wait_queue # <<>>
           THEN LET ProcessWaiters(queue, t_states, l_state, r_count) ==
                    IF queue = <<>> THEN <<t_states, l_state, queue, r_count>>
                    ELSE LET first == Head(queue)
                         rest == Tail(queue)
                         IN IF t_states[first] = "waiting_write"
                            THEN ProcessWaiters(rest, [t_states EXCEPT ![first] = "writing"], WRITER, r_count)
                            ELSE IF t_states[first] = "waiting_upread"
                                 THEN ProcessWaiters(rest, [t_states EXCEPT ![first] = "upreading"], l_state + UPGRADEABLE_READER, r_count)
                                 ELSE IF t_states[first] = "waiting_read"
                                      THEN ProcessWaiters(rest, [t_states EXCEPT ![first] = "reading"], l_state + 1, [r_count EXCEPT ![first] = r_count[first] + 1])
                                      ELSE ProcessWaiters(rest, t_states, l_state, r_count)
                result == ProcessWaiters(wait_queue, new_thread_states, new_lock_state, new_reader_count)
            IN /\ thread_states' = result[1]
               /\ lock_state' = result[2]
               /\ wait_queue' = result[3]
               /\ reader_count' = result[4]
           ELSE /\ UNCHANGED <<wait_queue, reader_count>>

(* Upgrade action - from upread to write *)
Upgrade(t) ==
    /\ thread_states[t] = "upreading"
    /\ ~HasBeingUpgraded(lock_state)
    /\ lock_state' = lock_state + BEING_UPGRADED
    /\ thread_states' = [thread_states EXCEPT ![t] = "upgrading"]
    /\ UNCHANGED <<wait_queue, reader_count>>

(* Complete upgrade - atomic transition *)
CompleteUpgrade(t) ==
    /\ thread_states[t] = "upgrading"
    /\ ReaderCount(lock_state) = 0
    /\ lock_state' = (lock_state - BEING_UPGRADED - UPGRADEABLE_READER) + WRITER
    /\ thread_states' = [thread_states EXCEPT ![t] = "writing"]
    /\ UNCHANGED <<wait_queue, reader_count>>

(* Downgrade action - from write to upread *)
Downgrade(t) ==
    /\ thread_states[t] = "writing"
    /\ lock_state' = (lock_state - WRITER) + UPGRADEABLE_READER
    /\ thread_states' = [thread_states EXCEPT ![t] = "upreading"]
    /\ UNCHANGED <<wait_queue, reader_count>>

(* Next-state relation *)
Next ==
    \/ \E t \in Threads: TryRead(t)
    \/ \E t \in Threads: Read(t)
    \/ \E t \in Threads: TryWrite(t)
    \/ \E t \in Threads: Write(t)
    \/ \E t \in Threads: TryUpread(t)
    \/ \E t \in Threads: Upread(t)
    \/ \E t \in Threads: ReadRelease(t)
    \/ \E t \in Threads: WriteRelease(t)
    \/ \E t \in Threads: UpreadRelease(t)
    \/ \E t \in Threads: Upgrade(t)
    \/ \E t \in Threads: CompleteUpgrade(t)
    \/ \E t \in Threads: Downgrade(t)

(* Fairness assumptions *)
vars == <<lock_state, wait_queue, thread_states, reader_count>>

Spec == 
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Next)

====