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

TryRead(t) ==
    /\ t \in Threads
    /\ ~HasWriter
    /\ ~being_upgraded
    /\ t \notin readers
    /\ writer # t
    /\ upgradeable_reader # t
    /\ readers' = readers \cup {t}
    /\ UNCHANGED <<lock_state, wait_queue, writer, upgradeable_reader, being_upgraded>>

TryWrite(t) ==
    /\ t \in Threads
    /\ ~HasWriter
    /\ ~HasUpgradeableReader
    /\ ~HasReaders
    /\ t \notin readers
    /\ writer' = t
    /\ UNCHANGED <<lock_state, wait_queue, readers, upgradeable_reader, being_upgraded>>

TryUpread(t) ==
    /\ t \in Threads
    /\ ~HasWriter
    /\ ~HasUpgradeableReader
    /\ t \notin readers
    /\ writer # t
    /\ upgradeable_reader' = t
    /\ UNCHANGED <<lock_state, wait_queue, readers, writer, being_upgraded>>

Read(t) ==
    IF TryRead(t)!1
    THEN TryRead(t)
    ELSE /\ wait_queue' = Append(wait_queue, t)
         /\ UNCHANGED <<lock_state, readers, writer, upgradeable_reader, being_upgraded>>

Write(t) ==
    IF TryWrite(t)!1
    THEN TryWrite(t)
    ELSE /\ wait_queue' = Append(wait_queue, t)
         /\ UNCHANGED <<lock_state, readers, writer, upgradeable_reader, being_upgraded>>

Upread(t) ==
    IF TryUpread(t)!1
    THEN TryUpread(t)
    ELSE /\ wait_queue' = Append(wait_queue, t)
         /\ UNCHANGED <<lock_state, readers, writer, upgradeable_reader, being_upgraded>>

ReleaseRead(t) ==
    /\ t \in readers
    /\ readers' = readers \ {t}
    /\ IF readers' = {} /\ wait_queue # <<>>
       THEN /\ wait_queue' = Tail(wait_queue)
            /\ UNCHANGED <<lock_state, writer, upgradeable_reader, being_upgraded>>
       ELSE UNCHANGED <<lock_state, wait_queue, writer, upgradeable_reader, being_upgraded>>

ReleaseWrite(t) ==
    /\ writer = t
    /\ writer' = NULL
    /\ IF wait_queue # <<>>
       THEN wait_queue' = <<>>
       ELSE UNCHANGED wait_queue
    /\ UNCHANGED <<lock_state, readers, upgradeable_reader, being_upgraded>>

ReleaseUpread(t) ==
    /\ upgradeable_reader = t
    /\ upgradeable_reader' = NULL
    /\ being_upgraded' = FALSE
    /\ IF wait_queue # <<>>
       THEN wait_queue' = <<>>
       ELSE UNCHANGED wait_queue
    /\ UNCHANGED <<lock_state, readers, writer>>

StartUpgrade(t) ==
    /\ upgradeable_reader = t
    /\ ~being_upgraded
    /\ being_upgraded' = TRUE
    /\ UNCHANGED <<lock_state, wait_queue, readers, writer, upgradeable_reader>>

CompleteUpgrade(t) ==
    /\ upgradeable_reader = t
    /\ being_upgraded
    /\ ~HasReaders
    /\ writer' = t
    /\ upgradeable_reader' = NULL
    /\ being_upgraded' = FALSE
    /\ UNCHANGED <<lock_state, wait_queue, readers>>

Downgrade(t) ==
    /\ writer = t
    /\ writer' = NULL
    /\ upgradeable_reader' = t
    /\ UNCHANGED <<lock_state, wait_queue, readers, being_upgraded>>

ProcessWaitQueue ==
    /\ wait_queue # <<>>
    /\ LET next_thread == Head(wait_queue)
       IN \/ /\ TryRead(next_thread)!1
             /\ TryRead(next_thread)
             /\ wait_queue' = Tail(wait_queue)
          \/ /\ TryWrite(next_thread)!1
             /\ TryWrite(next_thread)
             /\ wait_queue' = Tail(wait_queue)
          \/ /\ TryUpread(next_thread)!1
             /\ TryUpread(next_thread)
             /\ wait_queue' = Tail(wait_queue)
          \/ UNCHANGED Vars

Next ==
    \/ \E t \in Threads : Read(t)
    \/ \E t \in Threads : Write(t)
    \/ \E t \in Threads : Upread(t)
    \/ \E t \in Threads : ReleaseRead(t)
    \/ \E t \in Threads : ReleaseWrite(t)
    \/ \E t \in Threads : ReleaseUpread(t)
    \/ \E t \in Threads : StartUpgrade(t)
    \/ \E t \in Threads : CompleteUpgrade(t)
    \/ \E t \in Threads : Downgrade(t)
    \/ ProcessWaitQueue

Spec == Init /\ [][Next]_Vars /\ WF_Vars(Next)

====