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

TryRead(t) ==
    /\ t \notin readers
    /\ writer = NULL
    /\ upgradeable_reader = NULL \/ ~being_upgraded
    /\ ~being_upgraded
    /\ readers' = readers \cup {t}
    /\ UNCHANGED <<lock_state, wait_queue, writer, upgradeable_reader, being_upgraded>>

TryWrite(t) ==
    /\ writer = NULL
    /\ readers = {}
    /\ upgradeable_reader = NULL
    /\ ~being_upgraded
    /\ writer' = t
    /\ UNCHANGED <<lock_state, wait_queue, readers, upgradeable_reader, being_upgraded>>

TryUpread(t) ==
    /\ upgradeable_reader = NULL
    /\ writer = NULL
    /\ upgradeable_reader' = t
    /\ UNCHANGED <<lock_state, wait_queue, readers, writer, being_upgraded>>

Read(t) ==
    \/ TryRead(t)
    \/ /\ ~(writer = NULL /\ (upgradeable_reader = NULL \/ ~being_upgraded) /\ ~being_upgraded)
       /\ t \notin {x : x \in Range(wait_queue)}
       /\ wait_queue' = Append(wait_queue, t)
       /\ UNCHANGED <<lock_state, readers, writer, upgradeable_reader, being_upgraded>>

Write(t) ==
    \/ TryWrite(t)
    \/ /\ ~(writer = NULL /\ readers = {} /\ upgradeable_reader = NULL /\ ~being_upgraded)
       /\ t \notin {x : x \in Range(wait_queue)}
       /\ wait_queue' = Append(wait_queue, t)
       /\ UNCHANGED <<lock_state, readers, writer, upgradeable_reader, being_upgraded>>

Upread(t) ==
    \/ TryUpread(t)
    \/ /\ ~(upgradeable_reader = NULL /\ writer = NULL)
       /\ t \notin {x : x \in Range(wait_queue)}
       /\ wait_queue' = Append(wait_queue, t)
       /\ UNCHANGED <<lock_state, readers, writer, upgradeable_reader, being_upgraded>>

ReleaseRead(t) ==
    /\ t \in readers
    /\ readers' = readers \ {t}
    /\ IF readers' = {} /\ Len(wait_queue) > 0
       THEN /\ wait_queue' = Tail(wait_queue)
       ELSE /\ UNCHANGED wait_queue
    /\ UNCHANGED <<lock_state, writer, upgradeable_reader, being_upgraded>>

ReleaseWrite(t) ==
    /\ writer = t
    /\ writer' = NULL
    /\ IF Len(wait_queue) > 0
       THEN /\ \E new_queue \in {SubSeq(wait_queue, i, Len(wait_queue)) : i \in 1..Len(wait_queue)+1} :
                wait_queue' = new_queue
       ELSE /\ UNCHANGED wait_queue
    /\ UNCHANGED <<lock_state, readers, upgradeable_reader, being_upgraded>>

ReleaseUpread(t) ==
    /\ upgradeable_reader = t
    /\ upgradeable_reader' = NULL
    /\ being_upgraded' = FALSE
    /\ IF Len(wait_queue) > 0
       THEN /\ \E new_queue \in {SubSeq(wait_queue, i, Len(wait_queue)) : i \in 1..Len(wait_queue)+1} :
                wait_queue' = new_queue
       ELSE /\ UNCHANGED wait_queue
    /\ UNCHANGED <<lock_state, readers, writer>>

StartUpgrade(t) ==
    /\ upgradeable_reader = t
    /\ ~being_upgraded
    /\ being_upgraded' = TRUE
    /\ UNCHANGED <<lock_state, wait_queue, readers, writer, upgradeable_reader>>

CompleteUpgrade(t) ==
    /\ upgradeable_reader = t
    /\ being_upgraded
    /\ readers = {}
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
    /\ Len(wait_queue) > 0
    /\ LET next_thread == Head(wait_queue) IN
       \/ /\ writer = NULL
          /\ (upgradeable_reader = NULL \/ ~being_upgraded)
          /\ ~being_upgraded
          /\ readers' = readers \cup {next_thread}
          /\ wait_queue' = Tail(wait_queue)
          /\ UNCHANGED <<lock_state, writer, upgradeable_reader, being_upgraded>>
       \/ /\ writer = NULL
          /\ readers = {}
          /\ upgradeable_reader = NULL
          /\ ~being_upgraded
          /\ writer' = next_thread
          /\ wait_queue' = Tail(wait_queue)
          /\ UNCHANGED <<lock_state, readers, upgradeable_reader, being_upgraded>>
       \/ /\ upgradeable_reader = NULL
          /\ writer = NULL
          /\ upgradeable_reader' = next_thread
          /\ wait_queue' = Tail(wait_queue)
          /\ UNCHANGED <<lock_state, readers, writer, being_upgraded>>

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

Spec == Init /\ [][Next]_Vars
        /\ \A t \in Threads : WF_Vars(ReleaseRead(t))
        /\ \A t \in Threads : WF_Vars(ReleaseWrite(t))
        /\ \A t \in Threads : WF_Vars(ReleaseUpread(t))
        /\ \A t \in Threads : WF_Vars(CompleteUpgrade(t))
        /\ WF_Vars(ProcessWaitQueue)

====