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

NULL == "NULL"

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

CanTryRead(t) ==
    /\ t \notin read_guards
    /\ write_guard = NULL
    /\ upread_guard = NULL
    /\ ~being_upgraded
    /\ ~lock_state.writer

CanTryWrite(t) ==
    /\ write_guard = NULL
    /\ upread_guard = NULL
    /\ read_guards = {}
    /\ lock_state.reader_count = 0
    /\ ~lock_state.writer
    /\ ~lock_state.upgradeable_reader

CanTryUpread(t) ==
    /\ upread_guard = NULL
    /\ write_guard = NULL
    /\ ~lock_state.writer
    /\ ~lock_state.upgradeable_reader

Read(t) ==
    \/ TryRead(t)
    \/ (/\ ~CanTryRead(t)
        /\ wait_queue' = Append(wait_queue, <<t, "read">>)
        /\ UNCHANGED <<lock_state, read_guards, write_guard, upread_guard, being_upgraded>>)

Write(t) ==
    \/ TryWrite(t)
    \/ (/\ ~CanTryWrite(t)
        /\ wait_queue' = Append(wait_queue, <<t, "write">>)
        /\ UNCHANGED <<lock_state, read_guards, write_guard, upread_guard, being_upgraded>>)

Upread(t) ==
    \/ TryUpread(t)
    \/ (/\ ~CanTryUpread(t)
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
    /\ LET waiting_indices == {i \in 1..Len(wait_queue) : wait_queue[i][2] \in {"read", "write", "upread"}}
       IN IF waiting_indices # {}
          THEN LET read_threads == {wait_queue[i][1] : i \in waiting_indices /\ wait_queue[i][2] = "read"}
                   write_threads == {wait_queue[i][1] : i \in waiting_indices /\ wait_queue[i][2] = "write"}
                   upread_threads == {wait_queue[i][1] : i \in waiting_indices /\ wait_queue[i][2] = "upread"}
               IN /\ wait_queue' = <<>>
                  /\ IF read_threads # {} /\ write_threads = {} /\ upread_threads = {}
                     THEN /\ read_guards' = read_guards \cup read_threads
                          /\ lock_state' = [lock_state' EXCEPT !.reader_count = @ + Cardinality(read_threads)]
                          /\ UNCHANGED <<upread_guard, being_upgraded>>
                     ELSE IF write_threads # {} /\ Cardinality(write_threads) = 1
                     THEN /\ write_guard' = CHOOSE t_w \in write_threads : TRUE
                          /\ lock_state' = [lock_state' EXCEPT !.writer = TRUE]
                          /\ UNCHANGED <<read_guards, upread_guard, being_upgraded>>
                     ELSE IF upread_threads # {} /\ Cardinality(upread_threads) = 1
                     THEN /\ upread_guard' = CHOOSE t_u \in upread_threads : TRUE
                          /\ lock_state' = [lock_state' EXCEPT !.upgradeable_reader = TRUE]
                          /\ UNCHANGED <<read_guards, being_upgraded>>
                     ELSE UNCHANGED <<read_guards, upread_guard, being_upgraded>>
          ELSE UNCHANGED <<wait_queue, read_guards, upread_guard, being_upgraded>>

ReleaseUpread(t) ==
    /\ upread_guard = t
    /\ upread_guard' = NULL
    /\ lock_state' = [lock_state EXCEPT !.upgradeable_reader = FALSE]
    /\ being_upgraded' = FALSE
    /\ LET waiting_indices == {i \in 1..Len(wait_queue) : wait_queue[i][2] \in {"read", "write", "upread"}}
       IN IF waiting_indices # {}
          THEN LET read_threads == {wait_queue[i][1] : i \in waiting_indices /\ wait_queue[i][2] = "read"}
                   write_threads == {wait_queue[i][1] : i \in waiting_indices /\ wait_queue[i][2] = "write"}
                   upread_threads == {wait_queue[i][1] : i \in waiting_indices /\ wait_queue[i][2] = "upread"}
               IN /\ wait_queue' = <<>>
                  /\ IF read_threads # {} /\ write_threads = {} /\ upread_threads = {}
                     THEN /\ read_guards' = read_guards \cup read_threads
                          /\ lock_state' = [lock_state' EXCEPT !.reader_count = @ + Cardinality(read_threads)]
                     ELSE IF write_threads # {} /\ Cardinality(write_threads) = 1
                     THEN /\ write_guard' = CHOOSE t_w \in write_threads : TRUE
                          /\ lock_state' = [lock_state' EXCEPT !.writer = TRUE]
                          /\ UNCHANGED read_guards
                     ELSE IF upread_threads # {} /\ Cardinality(upread_threads) = 1
                     THEN /\ upread_guard' = CHOOSE t_u \in upread_threads : TRUE
                          /\ lock_state' = [lock_state' EXCEPT !.upgradeable_reader = TRUE]
                          /\ UNCHANGED read_guards
                     ELSE UNCHANGED read_guards
          ELSE UNCHANGED <<wait_queue, read_guards>>

Upgrade(t) ==
    /\ upread_guard = t
    /\ lock_state.upgradeable_reader = TRUE
    /\ being_upgraded' = TRUE
    /\ IF read_guards = {} /\ lock_state.reader_count = 0
       THEN /\ write_guard' = t
            /\ upread_guard' = NULL
            /\ lock_state' = [writer |-> TRUE, upgradeable_reader |-> FALSE, reader_count |-> 0]
            /\ being_upgraded' = FALSE
            /\ UNCHANGED <<wait_queue, read_guards>>
       ELSE UNCHANGED <<wait_queue, read_guards, write_guard, upread_guard, lock_state>>

Downgrade(t) ==
    /\ write_guard = t
    /\ write_guard' = NULL
    /\ upread_guard' = t
    /\ lock_state' = [writer |-> FALSE, upgradeable_reader |-> TRUE, reader_count |-> lock_state.reader_count]
    /\ UNCHANGED <<wait_queue, read_guards, being_upgraded>>

Next ==
    \/ \E t \in Threads : Read(t)
    \/ \E t \in Threads : Write(t)
    \/ \E t \in Threads : Upread(t)
    \/ \E t \in Threads : ReleaseRead(t)
    \/ \E t \in Threads : ReleaseWrite(t)
    \/ \E t \in Threads : ReleaseUpread(t)
    \/ \E t \in Threads : Upgrade(t)
    \/ \E t \in Threads : Downgrade(t)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

====