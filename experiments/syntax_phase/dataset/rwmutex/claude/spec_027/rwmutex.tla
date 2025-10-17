---- MODULE rwmutex ----

EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Threads, NULL

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
    /\ wait_queue \in Seq(Threads \X {"read", "write", "upread"})
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

CanAcquireRead ==
    /\ ~lock_state.writer
    /\ ~being_upgraded

CanAcquireWrite ==
    /\ ~lock_state.writer
    /\ ~lock_state.upgradeable_reader
    /\ lock_state.reader_count = 0

CanAcquireUpread ==
    /\ ~lock_state.writer
    /\ ~lock_state.upgradeable_reader

TryRead(t) ==
    /\ t \notin read_guards
    /\ write_guard # t
    /\ upread_guard # t
    /\ CanAcquireRead
    /\ lock_state' = [lock_state EXCEPT !.reader_count = @ + 1]
    /\ read_guards' = read_guards \cup {t}
    /\ UNCHANGED <<wait_queue, write_guard, upread_guard, being_upgraded>>

TryWrite(t) ==
    /\ write_guard = NULL
    /\ t \notin read_guards
    /\ upread_guard # t
    /\ CanAcquireWrite
    /\ lock_state' = [lock_state EXCEPT !.writer = TRUE]
    /\ write_guard' = t
    /\ UNCHANGED <<wait_queue, read_guards, upread_guard, being_upgraded>>

TryUpread(t) ==
    /\ upread_guard = NULL
    /\ t \notin read_guards
    /\ write_guard # t
    /\ CanAcquireUpread
    /\ lock_state' = [lock_state EXCEPT !.upgradeable_reader = TRUE]
    /\ upread_guard' = t
    /\ UNCHANGED <<wait_queue, read_guards, write_guard, being_upgraded>>

EnqueueRead(t) ==
    /\ t \notin read_guards
    /\ write_guard # t
    /\ upread_guard # t
    /\ ~CanAcquireRead
    /\ wait_queue' = Append(wait_queue, <<t, "read">>)
    /\ UNCHANGED <<lock_state, read_guards, write_guard, upread_guard, being_upgraded>>

EnqueueWrite(t) ==
    /\ write_guard = NULL
    /\ t \notin read_guards
    /\ upread_guard # t
    /\ ~CanAcquireWrite
    /\ wait_queue' = Append(wait_queue, <<t, "write">>)
    /\ UNCHANGED <<lock_state, read_guards, write_guard, upread_guard, being_upgraded>>

EnqueueUpread(t) ==
    /\ upread_guard = NULL
    /\ t \notin read_guards
    /\ write_guard # t
    /\ ~CanAcquireUpread
    /\ wait_queue' = Append(wait_queue, <<t, "upread">>)
    /\ UNCHANGED <<lock_state, read_guards, write_guard, upread_guard, being_upgraded>>

ReleaseRead(t) ==
    /\ t \in read_guards
    /\ lock_state' = [lock_state EXCEPT !.reader_count = @ - 1]
    /\ read_guards' = read_guards \ {t}
    /\ IF lock_state'.reader_count = 0 /\ Len(wait_queue) > 0
       THEN LET next_waiter == Head(wait_queue)
            IN /\ wait_queue' = Tail(wait_queue)
               /\ CASE next_waiter[2] = "write" ->
                       IF CanAcquireWrite
                       THEN /\ lock_state' = [lock_state' EXCEPT !.writer = TRUE]
                            /\ write_guard' = next_waiter[1]
                            /\ UNCHANGED upread_guard
                       ELSE /\ UNCHANGED <<write_guard, upread_guard>>
                    [] next_waiter[2] = "upread" ->
                       IF CanAcquireUpread
                       THEN /\ lock_state' = [lock_state' EXCEPT !.upgradeable_reader = TRUE]
                            /\ upread_guard' = next_waiter[1]
                            /\ UNCHANGED write_guard
                       ELSE /\ UNCHANGED <<write_guard, upread_guard>>
                    [] OTHER -> UNCHANGED <<write_guard, upread_guard>>
       ELSE UNCHANGED <<wait_queue, write_guard, upread_guard>>
    /\ UNCHANGED being_upgraded

ReleaseWrite(t) ==
    /\ write_guard = t
    /\ lock_state' = [lock_state EXCEPT !.writer = FALSE]
    /\ write_guard' = NULL
    /\ ProcessWaitQueue
    /\ UNCHANGED <<read_guards, upread_guard, being_upgraded>>

ReleaseUpread(t) ==
    /\ upread_guard = t
    /\ lock_state' = [lock_state EXCEPT !.upgradeable_reader = FALSE]
    /\ upread_guard' = NULL
    /\ ProcessWaitQueue
    /\ UNCHANGED <<read_guards, write_guard, being_upgraded>>

ProcessWaitQueue ==
    /\ wait_queue' = <<>>
    /\ LET readers == {w[1] : w \in {wait_queue[i] : i \in 1..Len(wait_queue)} |> w[2] = "read"}
           writers == {w[1] : w \in {wait_queue[i] : i \in 1..Len(wait_queue)} |> w[2] = "write"}
           upreaders == {w[1] : w \in {wait_queue[i] : i \in 1..Len(wait_queue)} |> w[2] = "upread"}
       IN IF CanAcquireWrite /\ writers # {}
          THEN /\ \E w \in writers:
                  /\ write_guard' = w
                  /\ lock_state' = [lock_state' EXCEPT !.writer = TRUE]
               /\ UNCHANGED <<read_guards, upread_guard>>
          ELSE IF CanAcquireRead /\ readers # {}
               THEN /\ read_guards' = read_guards \cup readers
                    /\ lock_state' = [lock_state' EXCEPT !.reader_count = @ + Cardinality(readers)]
                    /\ UNCHANGED <<write_guard, upread_guard>>
               ELSE IF CanAcquireUpread /\ upreaders # {}
                    THEN /\ \E u \in upreaders:
                            /\ upread_guard' = u
                            /\ lock_state' = [lock_state' EXCEPT !.upgradeable_reader = TRUE]
                         /\ UNCHANGED <<read_guards, write_guard>>
                    ELSE UNCHANGED <<read_guards, write_guard, upread_guard>>

StartUpgrade(t) ==
    /\ upread_guard = t
    /\ ~being_upgraded
    /\ being_upgraded' = TRUE
    /\ UNCHANGED <<lock_state, wait_queue, read_guards, write_guard, upread_guard>>

CompleteUpgrade(t) ==
    /\ upread_guard = t
    /\ being_upgraded
    /\ lock_state.reader_count = 0
    /\ lock_state' = [writer |-> TRUE, upgradeable_reader |-> TRUE, reader_count |-> 0]
    /\ write_guard' = t
    /\ being_upgraded' = FALSE
    /\ UNCHANGED <<wait_queue, read_guards, upread_guard>>

Downgrade(t) ==
    /\ write_guard = t
    /\ lock_state' = [writer |-> FALSE, upgradeable_reader |-> TRUE, reader_count |-> 0]
    /\ write_guard' = NULL
    /\ upread_guard' = t
    /\ UNCHANGED <<wait_queue, read_guards, being_upgraded>>

Next ==
    \/ \E t \in Threads:
        \/ TryRead(t)
        \/ TryWrite(t)
        \/ TryUpread(t)
        \/ EnqueueRead(t)
        \/ EnqueueWrite(t)
        \/ EnqueueUpread(t)
        \/ ReleaseRead(t)
        \/ ReleaseWrite(t)
        \/ ReleaseUpread(t)
        \/ StartUpgrade(t)
        \/ CompleteUpgrade(t)
        \/ Downgrade(t)

Spec ==
    Init /\ [][Next]_vars /\ WF_vars(Next)

====