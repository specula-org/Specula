---- MODULE rwmutex ----

EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Threads

VARIABLES
    lock_state,
    wait_queue,
    read_guards,
    write_guard,
    upread_guard,
    being_upgraded

vars == <<lock_state, wait_queue, read_guards, write_guard, upread_guard, being_upgraded>>

TypeOK ==
    /\ lock_state \in [writer: BOOLEAN, upgradeable_reader: BOOLEAN, reader_count: Nat]
    /\ wait_queue \in Seq(Threads \times {"read", "write", "upread"})
    /\ read_guards \subseteq Threads
    /\ write_guard \in Threads \cup {NULL}
    /\ upread_guard \in Threads \cup {NULL}
    /\ being_upgraded \in BOOLEAN

Init ==
    /\ lock_state = [writer |-> FALSE, upgradeable_reader |-> FALSE, reader_count |-> 0]
    /\ wait_queue = <<>>
    /\ read_guards = {}
    /\ write_guard = NULL
    /\ upread_guard = NULL
    /\ being_upgraded = FALSE

TryRead(t) ==
    /\ t \notin read_guards
    /\ write_guard = NULL
    /\ upread_guard = NULL
    /\ ~being_upgraded
    /\ ~lock_state.writer
    /\ lock_state' = [lock_state EXCEPT !.reader_count = @ + 1]
    /\ read_guards' = read_guards \cup {t}
    /\ UNCHANGED <<wait_queue, write_guard, upread_guard, being_upgraded>>

TryWrite(t) ==
    /\ write_guard = NULL
    /\ upread_guard = NULL
    /\ read_guards = {}
    /\ lock_state.reader_count = 0
    /\ ~lock_state.writer
    /\ ~lock_state.upgradeable_reader
    /\ lock_state' = [lock_state EXCEPT !.writer = TRUE]
    /\ write_guard' = t
    /\ UNCHANGED <<wait_queue, read_guards, upread_guard, being_upgraded>>

TryUpread(t) ==
    /\ upread_guard = NULL
    /\ write_guard = NULL
    /\ ~lock_state.writer
    /\ ~lock_state.upgradeable_reader
    /\ lock_state' = [lock_state EXCEPT !.upgradeable_reader = TRUE]
    /\ upread_guard' = t
    /\ UNCHANGED <<wait_queue, read_guards, write_guard, being_upgraded>>

Read(t) ==
    \/ TryRead(t)
    \/ (/\ ~TryRead(t)
        /\ wait_queue' = Append(wait_queue, <<t, "read">>)
        /\ UNCHANGED <<lock_state, read_guards, write_guard, upread_guard, being_upgraded>>)

Write(t) ==
    \/ TryWrite(t)
    \/ (/\ ~TryWrite(t)
        /\ wait_queue' = Append(wait_queue, <<t, "write">>)
        /\ UNCHANGED <<lock_state, read_guards, write_guard, upread_guard, being_upgraded>>)

Upread(t) ==
    \/ TryUpread(t)
    \/ (/\ ~TryUpread(t)
        /\ wait_queue' = Append(wait_queue, <<t, "upread">>)
        /\ UNCHANGED <<lock_state, read_guards, write_guard, upread_guard, being_upgraded>>)

ReleaseRead(t) ==
    /\ t \in read_guards
    /\ read_guards' = read_guards \ {t}
    /\ lock_state' = [lock_state EXCEPT !.reader_count = @ - 1]
    /\ IF lock_state'.reader_count = 0 /\ wait_queue # <<>>
       THEN LET head == Head(wait_queue)
                thread == head[1]
                op_type == head[2]
            IN /\ wait_queue' = Tail(wait_queue)
               /\ IF op_type = "write"
                  THEN /\ write_guard' = thread
                       /\ lock_state' = [lock_state' EXCEPT !.writer = TRUE]
                       /\ UNCHANGED <<upread_guard, being_upgraded>>
                  ELSE UNCHANGED <<write_guard, upread_guard, being_upgraded>>
       ELSE UNCHANGED <<wait_queue, write_guard, upread_guard, being_upgraded>>

ReleaseWrite(t) ==
    /\ write_guard = t
    /\ write_guard' = NULL
    /\ lock_state' = [lock_state EXCEPT !.writer = FALSE]
    /\ LET waiting_threads == {i \in 1..Len(wait_queue) : wait_queue[i][2] \in {"read", "write", "upread"}}
       IN IF waiting_threads # {}
          THEN LET readers == {i \in waiting_threads : wait_queue[i][2] = "read"}
                   writers == {i \in waiting_threads : wait_queue[i][2] = "write"}
                   upreaders == {i \in waiting_threads : wait_queue[i][2] = "upread"}
               IN IF readers # {} /\ writers = {} /\ upreaders = {}
                  THEN /\ read_guards' = read_guards \cup {wait_queue[i][1] : i \in readers}
                       /\ lock_state' = [lock_state' EXCEPT !.reader_count = @ + Cardinality(readers)]
                       /\ wait_queue' = SelectSeq(wait_queue, LAMBDA x: x[2] \notin {"read"})
                       /\ UNCHANGED <<upread_guard, being_upgraded>>
                  ELSE IF writers # {}
                       THEN LET first_writer == CHOOSE i \in writers : \A j \in writers : i <= j
                            IN /\ write_guard' = wait_queue[first_writer][1]
                               /\ lock_state' = [lock_state' EXCEPT !.writer = TRUE]
                               /\ wait_queue' = RemoveAt(wait_queue, first_writer)
                               /\ UNCHANGED <<read_guards, upread_guard, being_upgraded>>
                       ELSE UNCHANGED <<wait_queue, read_guards, upread_guard, being_upgraded>>
          ELSE UNCHANGED <<wait_queue, read_guards, upread_guard, being_upgraded>>

ReleaseUpread(t) ==
    /\ upread_guard = t
    /\ upread_guard' = NULL
    /\ lock_state' = [lock_state EXCEPT !.upgradeable_reader = FALSE]
    /\ being_upgraded' = FALSE
    /\ LET waiting_threads == {i \in 1..Len(wait_queue) : wait_queue[i][2] \in {"read", "write", "upread"}}
       IN IF waiting_threads # {}
          THEN LET readers == {i \in waiting_threads : wait_queue[i][2] = "read"}
                   writers == {i \in waiting_threads : wait_queue[i][2] = "write"}
                   upreaders == {i \in waiting_threads : wait_queue[i][2] = "upread"}
               IN IF readers # {} /\ writers = {} /\ upreaders = {}
                  THEN /\ read_guards' = read_guards \cup {wait_queue[i][1] : i \in readers}
                       /\ lock_state' = [lock_state' EXCEPT !.reader_count = @ + Cardinality(readers)]
                       /\ wait_queue' = SelectSeq(wait_queue, LAMBDA x: x[2] \notin {"read"})
                  ELSE IF writers # {}
                       THEN LET first_writer == CHOOSE i \in writers : \A j \in writers : i <= j
                            IN /\ write_guard' = wait_queue[first_writer][1]
                               /\ lock_state' = [lock_state' EXCEPT !.writer = TRUE]
                               /\ wait_queue' = RemoveAt(wait_queue, first_writer)
                               /\ UNCHANGED read_guards
                       ELSE IF upreaders # {}
                            THEN LET first_upreader == CHOOSE i \in upreaders : \A j \in upreaders : i <= j
                                 IN /\ upread_guard' = wait_queue[first_upreader][1]
                                    /\ lock_state' = [lock_state' EXCEPT !.upgradeable_reader = TRUE]
                                    /\ wait_queue' = RemoveAt(wait_queue, first_upreader)
                                    /\ UNCHANGED read_guards
                            ELSE UNCHANGED <<wait_queue, read_guards>>
          ELSE UNCHANGED <<wait_queue, read_guards>>

Upgrade(t) ==
    /\ upread_guard = t
    /\ ~being_upgraded
    /\ being_upgraded' = TRUE
    /\ IF read_guards = {}
       THEN /\ write_guard' = t
            /\ upread_guard' = NULL
            /\ lock_state' = [lock_state EXCEPT !.writer = TRUE, !.upgradeable_reader = FALSE]
            /\ being_upgraded' = FALSE
       ELSE UNCHANGED <<write_guard, upread_guard, lock_state>>
    /\ UNCHANGED <<wait_queue, read_guards>>

TryUpgrade(t) ==
    /\ upread_guard = t
    /\ read_guards = {}
    /\ ~being_upgraded
    /\ write_guard' = t
    /\ upread_guard' = NULL
    /\ lock_state' = [lock_state EXCEPT !.writer = TRUE, !.upgradeable_reader = FALSE]
    /\ UNCHANGED <<wait_queue, read_guards, being_upgraded>>

Downgrade(t) ==
    /\ write_guard = t
    /\ write_guard' = NULL
    /\ upread_guard' = t
    /\ lock_state' = [lock_state EXCEPT !.writer = FALSE, !.upgradeable_reader = TRUE]
    /\ UNCHANGED <<wait_queue, read_guards, being_upgraded>>

Next ==
    \E t \in Threads :
        \/ Read(t)
        \/ Write(t)
        \/ Upread(t)
        \/ ReleaseRead(t)
        \/ ReleaseWrite(t)
        \/ ReleaseUpread(t)
        \/ Upgrade(t)
        \/ TryUpgrade(t)
        \/ Downgrade(t)

Spec ==
    Init /\ [][Next]_vars
    /\ \A t \in Threads : WF_vars(ReleaseRead(t))
    /\ \A t \in Threads : WF_vars(ReleaseWrite(t))
    /\ \A t \in Threads : WF_vars(ReleaseUpread(t))
    /\ \A t \in Threads : WF_vars(Upgrade(t))
    /\ \A t \in Threads : SF_vars(Read(t))
    /\ \A t \in Threads : SF_vars(Write(t))
    /\ \A t \in Threads : SF_vars(Upread(t))

====