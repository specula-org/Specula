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
            IN IF op_type = "write"
               THEN /\ wait_queue' = Tail(wait_queue)
                    /\ write_guard' = thread
                    /\ lock_state' = [lock_state' EXCEPT !.writer = TRUE]
                    /\ UNCHANGED <<upread_guard, being_upgraded>>
               ELSE /\ UNCHANGED <<wait_queue, write_guard, upread_guard, being_upgraded>>
       ELSE /\ UNCHANGED <<wait_queue, write_guard, upread_guard, being_upgraded>>

ReleaseWrite(t) ==
    /\ write_guard = t
    /\ write_guard' = NULL
    /\ lock_state' = [lock_state EXCEPT !.writer = FALSE]
    /\ LET readers == {i \in 1..Len(wait_queue) : wait_queue[i][2] = "read"}
           writers == {i \in 1..Len(wait_queue) : wait_queue[i][2] = "write"}
           upreaders == {i \in 1..Len(wait_queue) : wait_queue[i][2] = "upread"}
       IN IF readers # {}
          THEN LET reader_threads == {wait_queue[i][1] : i \in readers}
               IN /\ read_guards' = read_guards \cup reader_threads
                  /\ lock_state' = [lock_state' EXCEPT !.reader_count = @ + Cardinality(reader_threads)]
                  /\ wait_queue' = SelectSeq(wait_queue, LAMBDA x: x[2] # "read")
                  /\ UNCHANGED <<upread_guard, being_upgraded>>
          ELSE IF upreaders # {}
               THEN LET upread_thread == wait_queue[CHOOSE i \in upreaders : TRUE][1]
                    IN /\ upread_guard' = upread_thread
                       /\ lock_state' = [lock_state' EXCEPT !.upgradeable_reader = TRUE]
                       /\ wait_queue' = SelectSeq(wait_queue, LAMBDA x: x[1] # upread_thread \/ x[2] # "upread")
                       /\ UNCHANGED <<read_guards, being_upgraded>>
               ELSE IF writers # {}
                    THEN LET writer_thread == wait_queue[CHOOSE i \in writers : TRUE][1]
                         IN /\ write_guard' = writer_thread
                            /\ lock_state' = [lock_state' EXCEPT !.writer = TRUE]
                            /\ wait_queue' = SelectSeq(wait_queue, LAMBDA x: x[1] # writer_thread \/ x[2] # "write")
                            /\ UNCHANGED <<read_guards, upread_guard, being_upgraded>>
                    ELSE /\ UNCHANGED <<wait_queue, read_guards, upread_guard, being_upgraded>>

ReleaseUpread(t) ==
    /\ upread_guard = t
    /\ upread_guard' = NULL
    /\ lock_state' = [lock_state EXCEPT !.upgradeable_reader = FALSE]
    /\ being_upgraded' = FALSE
    /\ LET readers == {i \in 1..Len(wait_queue) : wait_queue[i][2] = "read"}
           writers == {i \in 1..Len(wait_queue) : wait_queue[i][2] = "write"}
           upreaders == {i \in 1..Len(wait_queue) : wait_queue[i][2] = "upread"}
       IN IF readers # {}
          THEN LET reader_threads == {wait_queue[i][1] : i \in readers}
               IN /\ read_guards' = read_guards \cup reader_threads
                  /\ lock_state' = [lock_state' EXCEPT !.reader_count = @ + Cardinality(reader_threads)]
                  /\ wait_queue' = SelectSeq(wait_queue, LAMBDA x: x[2] # "read")
          ELSE IF upreaders # {}
               THEN LET upread_thread == wait_queue[CHOOSE i \in upreaders : TRUE][1]
                    IN /\ upread_guard' = upread_thread
                       /\ lock_state' = [lock_state' EXCEPT !.upgradeable_reader = TRUE]
                       /\ wait_queue' = SelectSeq(wait_queue, LAMBDA x: x[1] # upread_thread \/ x[2] # "upread")
                       /\ UNCHANGED <<read_guards>>
               ELSE IF writers # {}
                    THEN LET writer_thread == wait_queue[CHOOSE i \in writers : TRUE][1]
                         IN /\ write_guard' = writer_thread
                            /\ lock_state' = [lock_state' EXCEPT !.writer = TRUE]
                            /\ wait_queue' = SelectSeq(wait_queue, LAMBDA x: x[1] # writer_thread \/ x[2] # "write")
                            /\ UNCHANGED <<read_guards>>
                    ELSE /\ UNCHANGED <<wait_queue, read_guards>>

Upgrade(t) ==
    /\ upread_guard = t
    /\ read_guards = {}
    /\ lock_state.reader_count = 0
    /\ being_upgraded' = TRUE
    /\ write_guard' = t
    /\ upread_guard' = NULL
    /\ lock_state' = [writer |-> TRUE, upgradeable_reader |-> FALSE, reader_count |-> 0]
    /\ UNCHANGED <<wait_queue, read_guards>>

Downgrade(t) ==
    /\ write_guard = t
    /\ write_guard' = NULL
    /\ upread_guard' = t
    /\ lock_state' = [writer |-> FALSE, upgradeable_reader |-> TRUE, reader_count |-> 0]
    /\ UNCHANGED <<wait_queue, read_guards, being_upgraded>>

Next ==
    \E t \in Threads:
        \/ Read(t)
        \/ Write(t)
        \/ Upread(t)
        \/ ReleaseRead(t)
        \/ ReleaseWrite(t)
        \/ ReleaseUpread(t)
        \/ Upgrade(t)
        \/ Downgrade(t)

Spec == Init /\ [][Next]_vars
            /\ \A t \in Threads: WF_vars(ReleaseRead(t))
            /\ \A t \in Threads: WF_vars(ReleaseWrite(t))
            /\ \A t \in Threads: WF_vars(ReleaseUpread(t))
            /\ \A t \in Threads: WF_vars(Upgrade(t))
            /\ \A t \in Threads: WF_vars(Downgrade(t))

====