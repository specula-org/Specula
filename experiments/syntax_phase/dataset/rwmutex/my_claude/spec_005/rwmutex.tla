---- MODULE rwmutex ----

EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Threads

VARIABLES
    lock_state,
    wait_queue,
    readers,
    writer,
    upgradeable_reader,
    being_upgraded

Vars == <<lock_state, wait_queue, readers, writer, upgradeable_reader, being_upgraded>>

TypeOK ==
    /\ lock_state \in Nat
    /\ wait_queue \in Seq(Threads)
    /\ readers \subseteq Threads
    /\ writer \in Threads \cup {NULL}
    /\ upgradeable_reader \in Threads \cup {NULL}
    /\ being_upgraded \in BOOLEAN

Init ==
    /\ lock_state = 0
    /\ wait_queue = <<>>
    /\ readers = {}
    /\ writer = NULL
    /\ upgradeable_reader = NULL
    /\ being_upgraded = FALSE

HasWriter == writer # NULL
HasUpgradeableReader == upgradeable_reader # NULL
HasReaders == readers # {}
ReaderCount == Cardinality(readers)

CanAcquireRead(t) ==
    /\ t \in Threads
    /\ ~HasWriter
    /\ ~being_upgraded

CanAcquireWrite(t) ==
    /\ t \in Threads
    /\ ~HasWriter
    /\ ~HasUpgradeableReader
    /\ ~HasReaders

CanAcquireUpread(t) ==
    /\ t \in Threads
    /\ ~HasWriter
    /\ ~HasUpgradeableReader

CanUpgrade(t) ==
    /\ t \in Threads
    /\ upgradeable_reader = t
    /\ ~HasWriter
    /\ ~HasReaders

TryRead(t) ==
    /\ CanAcquireRead(t)
    /\ readers' = readers \cup {t}
    /\ lock_state' = lock_state + 1
    /\ UNCHANGED <<wait_queue, writer, upgradeable_reader, being_upgraded>>

TryWrite(t) ==
    /\ CanAcquireWrite(t)
    /\ writer' = t
    /\ lock_state' = lock_state
    /\ UNCHANGED <<wait_queue, readers, upgradeable_reader, being_upgraded>>

TryUpread(t) ==
    /\ CanAcquireUpread(t)
    /\ upgradeable_reader' = t
    /\ lock_state' = lock_state
    /\ UNCHANGED <<wait_queue, readers, writer, being_upgraded>>

BlockingRead(t) ==
    /\ t \in Threads
    /\ ~CanAcquireRead(t)
    /\ wait_queue' = Append(wait_queue, t)
    /\ UNCHANGED <<lock_state, readers, writer, upgradeable_reader, being_upgraded>>

BlockingWrite(t) ==
    /\ t \in Threads
    /\ ~CanAcquireWrite(t)
    /\ wait_queue' = Append(wait_queue, t)
    /\ UNCHANGED <<lock_state, readers, writer, upgradeable_reader, being_upgraded>>

BlockingUpread(t) ==
    /\ t \in Threads
    /\ ~CanAcquireUpread(t)
    /\ wait_queue' = Append(wait_queue, t)
    /\ UNCHANGED <<lock_state, readers, writer, upgradeable_reader, being_upgraded>>

ReleaseRead(t) ==
    /\ t \in readers
    /\ readers' = readers \ {t}
    /\ lock_state' = lock_state - 1
    /\ IF readers' = {}
       THEN /\ wait_queue' = IF wait_queue = <<>> THEN <<>> ELSE Tail(wait_queue)
       ELSE /\ UNCHANGED wait_queue
    /\ UNCHANGED <<writer, upgradeable_reader, being_upgraded>>

ReleaseWrite(t) ==
    /\ writer = t
    /\ writer' = NULL
    /\ wait_queue' = <<>>
    /\ UNCHANGED <<lock_state, readers, upgradeable_reader, being_upgraded>>

ReleaseUpread(t) ==
    /\ upgradeable_reader = t
    /\ upgradeable_reader' = NULL
    /\ being_upgraded' = FALSE
    /\ wait_queue' = <<>>
    /\ UNCHANGED <<lock_state, readers, writer>>

StartUpgrade(t) ==
    /\ upgradeable_reader = t
    /\ ~being_upgraded
    /\ being_upgraded' = TRUE
    /\ UNCHANGED <<lock_state, wait_queue, readers, writer, upgradeable_reader>>

CompleteUpgrade(t) ==
    /\ upgradeable_reader = t
    /\ being_upgraded
    /\ CanUpgrade(t)
    /\ writer' = t
    /\ upgradeable_reader' = NULL
    /\ being_upgraded' = FALSE
    /\ UNCHANGED <<lock_state, wait_queue, readers>>

Downgrade(t) ==
    /\ writer = t
    /\ writer' = NULL
    /\ upgradeable_reader' = t
    /\ UNCHANGED <<lock_state, wait_queue, readers, being_upgraded>>

WakeFromQueue ==
    /\ wait_queue # <<>>
    /\ LET next_thread == Head(wait_queue)
       IN /\ wait_queue' = Tail(wait_queue)
          /\ \/ /\ CanAcquireRead(next_thread)
                /\ readers' = readers \cup {next_thread}
                /\ lock_state' = lock_state + 1
                /\ UNCHANGED <<writer, upgradeable_reader, being_upgraded>>
             \/ /\ CanAcquireWrite(next_thread)
                /\ writer' = next_thread
                /\ UNCHANGED <<lock_state, readers, upgradeable_reader, being_upgraded>>
             \/ /\ CanAcquireUpread(next_thread)
                /\ upgradeable_reader' = next_thread
                /\ UNCHANGED <<lock_state, readers, writer, being_upgraded>>
             \/ /\ ~CanAcquireRead(next_thread)
                /\ ~CanAcquireWrite(next_thread)
                /\ ~CanAcquireUpread(next_thread)
                /\ wait_queue' = Append(wait_queue', next_thread)
                /\ UNCHANGED <<lock_state, readers, writer, upgradeable_reader, being_upgraded>>

Next ==
    \/ \E t \in Threads : TryRead(t)
    \/ \E t \in Threads : TryWrite(t)
    \/ \E t \in Threads : TryUpread(t)
    \/ \E t \in Threads : BlockingRead(t)
    \/ \E t \in Threads : BlockingWrite(t)
    \/ \E t \in Threads : BlockingUpread(t)
    \/ \E t \in Threads : ReleaseRead(t)
    \/ \E t \in Threads : ReleaseWrite(t)
    \/ \E t \in Threads : ReleaseUpread(t)
    \/ \E t \in Threads : StartUpgrade(t)
    \/ \E t \in Threads : CompleteUpgrade(t)
    \/ \E t \in Threads : Downgrade(t)
    \/ WakeFromQueue

Spec == Init /\ [][Next]_Vars /\ WF_Vars(Next)

====