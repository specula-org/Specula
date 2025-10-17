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
    /\ IF lock_state'.reader_count = 0 /\ Len(wait_queue) > 0
       THEN LET head == Head(wait_queue)
                thread == head[1]
                op_type == head[2]
            IN /\ wait_queue' = Tail(wait_queue)
               /\ IF op_type = "write" /\ TryWrite(thread)
                  THEN write_guard' = thread /\ lock_state' = [lock_state' EXCEPT !.writer = TRUE]
                  ELSE UNCHANGED <<write_guard, upread_guard>>
       ELSE wait_queue' = wait_queue /\ UNCHANGED <<write_guard, upread_guard>>
    /\ UNCHANGED being_upgraded

ReleaseWrite(t) ==
    /\ write_guard = t
    /\ write_guard' = NULL
    /\ lock_state' = [lock_state EXCEPT !.writer = FALSE]
    /\ LET waiting_threads == {i \in 1..Len(wait_queue) : TRUE}
       IN /\ wait_queue' = <<>>
          /\ \A i \in waiting_threads :
                LET entry == wait_queue[i]
                    thread == entry[1]
                    op_type == entry[2]
                IN IF op_type = "read" /\ ~being_upgraded
                   THEN read_guards' = read_guards \cup {thread} /\ 
                        lock_state' = [lock_state' EXCEPT !.reader_count = @ + 1]
                   ELSE IF op_type = "upread" /\ ~lock_state'.upgradeable_reader
                   THEN upread_guard' = thread /\ 
                        lock_state' = [lock_state' EXCEPT !.upgradeable_reader = TRUE]
                   ELSE IF op_type = "write" /\ lock_state'.reader_count = 0 /\ upread_guard' = NULL
                   THEN write_guard' = thread /\ 
                        lock_state' = [lock_state' EXCEPT !.writer = TRUE]
                   ELSE UNCHANGED <<read_guards, upread_guard>>
    /\ UNCHANGED being_upgraded

ReleaseUpread(t) ==
    /\ upread_guard = t
    /\ upread_guard' = NULL
    /\ lock_state' = [lock_state EXCEPT !.upgradeable_reader = FALSE]
    /\ being_upgraded' = FALSE
    /\ LET waiting_threads == {i \in 1..Len(wait_queue) : TRUE}
       IN /\ wait_queue' = <<>>
          /\ \A i \in waiting_threads :
                LET entry == wait_queue[i]
                    thread == entry[1]
                    op_type == entry[2]
                IN IF op_type = "read"
                   THEN read_guards' = read_guards \cup {thread} /\ 
                        lock_state' = [lock_state' EXCEPT !.reader_count = @ + 1]
                   ELSE IF op_type = "upread"
                   THEN upread_guard' = thread /\ 
                        lock_state' = [lock_state' EXCEPT !.upgradeable_reader = TRUE]
                   ELSE IF op_type = "write" /\ lock_state'.reader_count = 0
                   THEN write_guard' = thread /\ 
                        lock_state' = [lock_state' EXCEPT !.writer = TRUE]
                   ELSE UNCHANGED <<read_guards, upread_guard>>

Upgrade(t) ==
    /\ upread_guard = t
    /\ ~being_upgraded
    /\ being_upgraded' = TRUE
    /\ IF read_guards = {}
       THEN /\ write_guard' = t
            /\ lock_state' = [lock_state EXCEPT !.writer = TRUE]
            /\ upread_guard' = NULL
            /\ being_upgraded' = FALSE
       ELSE UNCHANGED <<write_guard, upread_guard, lock_state>>
    /\ UNCHANGED <<wait_queue, read_guards>>

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