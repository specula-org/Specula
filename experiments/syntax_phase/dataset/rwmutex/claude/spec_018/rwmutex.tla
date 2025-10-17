---- MODULE rwmutex ----

EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Processes

VARIABLES 
    lock_state,
    wait_queue,
    readers,
    writers,
    upreaders,
    upgrading

Vars == <<lock_state, wait_queue, readers, writers, upreaders, upgrading>>

TypeOK == 
    /\ lock_state \in [writer: BOOLEAN, upgradeable_reader: BOOLEAN, being_upgraded: BOOLEAN, reader_count: Nat]
    /\ wait_queue \in Seq(Processes)
    /\ readers \subseteq Processes
    /\ writers \subseteq Processes  
    /\ upreaders \subseteq Processes
    /\ upgrading \subseteq Processes

Init ==
    /\ lock_state = [writer |-> FALSE, upgradeable_reader |-> FALSE, being_upgraded |-> FALSE, reader_count |-> 0]
    /\ wait_queue = <<>>
    /\ readers = {}
    /\ writers = {}
    /\ upreaders = {}
    /\ upgrading = {}

CanAcquireRead ==
    /\ ~lock_state.writer
    /\ ~lock_state.being_upgraded

CanAcquireWrite ==
    /\ ~lock_state.writer
    /\ ~lock_state.upgradeable_reader
    /\ lock_state.reader_count = 0

CanAcquireUpread ==
    /\ ~lock_state.writer
    /\ ~lock_state.upgradeable_reader

AcquireRead(p) ==
    /\ p \notin (readers \cup writers \cup upreaders)
    /\ CanAcquireRead
    /\ lock_state' = [lock_state EXCEPT !.reader_count = @ + 1]
    /\ readers' = readers \cup {p}
    /\ UNCHANGED <<wait_queue, writers, upreaders, upgrading>>

AcquireWrite(p) ==
    /\ p \notin (readers \cup writers \cup upreaders)
    /\ CanAcquireWrite
    /\ lock_state' = [lock_state EXCEPT !.writer = TRUE]
    /\ writers' = writers \cup {p}
    /\ UNCHANGED <<wait_queue, readers, upreaders, upgrading>>

AcquireUpread(p) ==
    /\ p \notin (readers \cup writers \cup upreaders)
    /\ CanAcquireUpread
    /\ lock_state' = [lock_state EXCEPT !.upgradeable_reader = TRUE]
    /\ upreaders' = upreaders \cup {p}
    /\ UNCHANGED <<wait_queue, readers, writers, upgrading>>

ReleaseRead(p) ==
    /\ p \in readers
    /\ lock_state' = [lock_state EXCEPT !.reader_count = @ - 1]
    /\ readers' = readers \ {p}
    /\ IF lock_state'.reader_count = 0 /\ wait_queue # <<>>
       THEN wait_queue' = Tail(wait_queue)
       ELSE wait_queue' = wait_queue
    /\ UNCHANGED <<writers, upreaders, upgrading>>

ReleaseWrite(p) ==
    /\ p \in writers
    /\ lock_state' = [lock_state EXCEPT !.writer = FALSE]
    /\ writers' = writers \ {p}
    /\ wait_queue' = <<>>
    /\ UNCHANGED <<readers, upreaders, upgrading>>

ReleaseUpread(p) ==
    /\ p \in upreaders
    /\ p \notin upgrading
    /\ lock_state' = [lock_state EXCEPT !.upgradeable_reader = FALSE]
    /\ upreaders' = upreaders \ {p}
    /\ wait_queue' = <<>>
    /\ UNCHANGED <<readers, writers, upgrading>>

StartUpgrade(p) ==
    /\ p \in upreaders
    /\ p \notin upgrading
    /\ lock_state' = [lock_state EXCEPT !.being_upgraded = TRUE]
    /\ upgrading' = upgrading \cup {p}
    /\ UNCHANGED <<wait_queue, readers, writers, upreaders>>

CompleteUpgrade(p) ==
    /\ p \in upgrading
    /\ lock_state.reader_count = 0
    /\ lock_state' = [lock_state EXCEPT !.writer = TRUE, !.being_upgraded = FALSE]
    /\ writers' = writers \cup {p}
    /\ upreaders' = upreaders \ {p}
    /\ upgrading' = upgrading \ {p}
    /\ UNCHANGED <<wait_queue, readers>>

Downgrade(p) ==
    /\ p \in writers
    /\ lock_state' = [lock_state EXCEPT !.writer = FALSE, !.upgradeable_reader = TRUE]
    /\ writers' = writers \ {p}
    /\ upreaders' = upreaders \cup {p}
    /\ UNCHANGED <<wait_queue, readers, upgrading>>

WaitForLock(p) ==
    /\ p \notin (readers \cup writers \cup upreaders)
    /\ p \notin Elems(wait_queue)
    /\ ~CanAcquireRead \/ ~CanAcquireWrite \/ ~CanAcquireUpread
    /\ wait_queue' = Append(wait_queue, p)
    /\ UNCHANGED <<lock_state, readers, writers, upreaders, upgrading>>

Next ==
    \E p \in Processes:
        \/ AcquireRead(p)
        \/ AcquireWrite(p)
        \/ AcquireUpread(p)
        \/ ReleaseRead(p)
        \/ ReleaseWrite(p)
        \/ ReleaseUpread(p)
        \/ StartUpgrade(p)
        \/ CompleteUpgrade(p)
        \/ Downgrade(p)
        \/ WaitForLock(p)

Spec == Init /\ [][Next]_Vars /\ WF_Vars(Next)

====