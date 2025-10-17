---- MODULE raftkvs ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Threads, Nil

READER == 1
BEING_UPGRADED == 1024 \* 1024
UPGRADEABLE_READER == 2 * BEING_UPGRADED
WRITER == 2 * UPGRADEABLE_READER

VARIABLES lock, readers, writer, upgrader, waiting_queue, proc_state

vars == <<lock, readers, writer, upgrader, waiting_queue, proc_state>>

TypeOK ==
    /\ lock \in Nat
    /\ readers \subseteq Threads
    /\ writer \in Threads \cup {Nil}
    /\ upgrader \in Threads \cup {Nil}
    /\ waiting_queue \in Seq(Threads)
    /\ proc_state \in [Threads -> {"idle", "reading", "writing", "upgradable_reading", "upgrading", "waiting"}]

ReaderCount(l) == l % BEING_UPGRADED
IsWriter(l) == (l \div WRITER) % 2 = 1
IsUpgrader(l) == (l \div UPGRADEABLE_READER) % 2 = 1
IsUpgrading(l) == (l \div BEING_UPGRADED) % 2 = 1

Init ==
    /\ lock = 0
    /\ readers = {}
    /\ writer = Nil
    /\ upgrader = Nil
    /\ waiting_queue = <<>>
    /\ proc_state = [t \in Threads |-> "idle"]

AcquireRead(t) ==
    /\ proc_state[t] = "idle"
    /\ IF ~IsWriter(lock) /\ ~IsUpgrading(lock)
       THEN /\ lock' = lock + READER
            /\ readers' = readers \cup {t}
            /\ proc_state' = [proc_state EXCEPT ![t] = "reading"]
            /\ UNCHANGED <<writer, upgrader, waiting_queue>>
       ELSE /\ waiting_queue' = Append(waiting_queue, t)
            /\ proc_state' = [proc_state EXCEPT ![t] = "waiting"]
            /\ UNCHANGED <<lock, readers, writer, upgrader>>

AcquireWrite(t) ==
    /\ proc_state[t] = "idle"
    /\ IF lock = 0
       THEN /\ lock' = WRITER
            /\ writer' = t
            /\ proc_state' = [proc_state EXCEPT ![t] = "writing"]
            /\ UNCHANGED <<readers, upgrader, waiting_queue>>
       ELSE /\ waiting_queue' = Append(waiting_queue, t)
            /\ proc_state' = [proc_state EXCEPT ![t] = "waiting"]
            /\ UNCHANGED <<lock, readers, writer, upgrader>>

AcquireUpRead(t) ==
    /\ proc_state[t] = "idle"
    /\ IF ~IsWriter(lock) /\ ~IsUpgrader(lock)
       THEN /\ lock' = lock + UPGRADEABLE_READER
            /\ upgrader' = t
            /\ proc_state' = [proc_state EXCEPT ![t] = "upgradable_reading"]
            /\ UNCHANGED <<readers, writer, waiting_queue>>
       ELSE /\ waiting_queue' = Append(waiting_queue, t)
            /\ proc_state' = [proc_state EXCEPT ![t] = "waiting"]
            /\ UNCHANGED <<lock, readers, writer, upgrader>>

ReleaseRead(t) ==
    /\ proc_state[t] = "reading"
    /\ LET new_lock == lock - READER IN
       /\ lock' = new_lock
       /\ readers' = readers \ {t}
       /\ IF new_lock = 0 /\ Len(waiting_queue) > 0
          THEN LET woken_proc == Head(waiting_queue) IN
               /\ proc_state' = [proc_state EXCEPT ![t] = "idle", ![woken_proc] = "idle"]
               /\ waiting_queue' = Tail(waiting_queue)
          ELSE /\ proc_state' = [proc_state EXCEPT ![t] = "idle"]
               /\ UNCHANGED waiting_queue
    /\ UNCHANGED <<writer, upgrader>>

ReleaseWrite(t) ==
    /\ proc_state[t] = "writing"
    /\ writer' = Nil
    /\ lock' = lock - WRITER
    /\ LET WokenProcs == {waiting_queue[i] : i \in 1..Len(waiting_queue)} IN
       /\ proc_state' = [p \in Threads |-> IF p = t \/ p \in WokenProcs THEN "idle" ELSE proc_state[p]]
       /\ waiting_queue' = <<>>
    /\ UNCHANGED <<readers, upgrader>>

ReleaseUpRead(t) ==
    /\ proc_state[t] = "upgradable_reading"
    /\ LET new_lock == lock - UPGRADEABLE_READER IN
       /\ lock' = new_lock
       /\ upgrader' = Nil
       /\ IF new_lock = 0 /\ Len(waiting_queue) > 0
          THEN LET WokenProcs == {waiting_queue[i] : i \in 1..Len(waiting_queue)} IN
               /\ proc_state' = [p \in Threads |-> IF p = t \/ p \in WokenProcs THEN "idle" ELSE proc_state[p]]
               /\ waiting_queue' = <<>>
          ELSE /\ proc_state' = [proc_state EXCEPT ![t] = "idle"]
               /\ UNCHANGED waiting_queue
    /\ UNCHANGED <<readers, writer>>

StartUpgrade(t) ==
    /\ proc_state[t] = "upgradable_reading"
    /\ upgrader = t
    /\ lock' = lock + BEING_UPGRADED
    /\ proc_state' = [proc_state EXCEPT ![t] = "upgrading"]
    /\ UNCHANGED <<readers, writer, upgrader, waiting_queue>>

CompleteUpgrade(t) ==
    /\ proc_state[t] = "upgrading"
    /\ upgrader = t
    /\ ReaderCount(lock) = 0
    /\ IsUpgrading(lock)
    /\ IsUpgrader(lock)
    /\ lock' = (lock - BEING_UPGRADED - UPGRADEABLE_READER) + WRITER
    /\ writer' = t
    /\ upgrader' = Nil
    /\ proc_state' = [proc_state EXCEPT ![t] = "writing"]
    /\ UNCHANGED <<readers, waiting_queue>>

Downgrade(t) ==
    /\ proc_state[t] = "writing"
    /\ writer = t
    /\ IsWriter(lock)
    /\ lock' = UPGRADEABLE_READER
    /\ writer' = Nil
    /\ upgrader' = t
    /\ proc_state' = [proc_state EXCEPT ![t] = "upgradable_reading"]
    /\ UNCHANGED <<readers, waiting_queue>>

Next ==
    \/ \E t \in Threads:
        \/ AcquireRead(t)
        \/ AcquireWrite(t)
        \/ AcquireUpRead(t)
        \/ ReleaseRead(t)
        \/ ReleaseWrite(t)
        \/ ReleaseUpRead(t)
        \/ StartUpgrade(t)
        \/ CompleteUpgrade(t)
        \/ Downgrade(t)

Spec == Init /\ [][Next]_vars /\
    \A t \in Threads:
        /\ WF_vars(ReleaseRead(t))
        /\ WF_vars(ReleaseWrite(t))
        /\ WF_vars(ReleaseUpRead(t))
        /\ WF_vars(StartUpgrade(t))
        /\ WF_vars(CompleteUpgrade(t))
        /\ WF_vars(Downgrade(t))

====