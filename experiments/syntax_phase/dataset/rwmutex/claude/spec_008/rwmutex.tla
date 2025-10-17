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
    /\ IF lock_state'.reader_count = 0
       THEN /\ wait_queue' = IF Len(wait_queue) > 0 THEN Tail(wait_queue) ELSE <<>>
            /\ LET next_waiter == IF Len(wait_queue) > 0 THEN Head(wait_queue) ELSE NULL
               IN IF next_waiter # NULL
                  THEN CASE next_waiter[2] = "write" ->
                            /\ CanAcquireWrite
                            /\ lock_state' = [lock_state' EXCEPT !.writer = TRUE]
                            /\ write_guard' = next_waiter[1]
                            /\ UNCHANGED <<upread_guard, being_upgraded>>
                       [] next_waiter[2] = "upread" ->
                            /\ CanAcquireUpread
                            /\ lock_state' = [lock_state' EXCEPT !.upgradeable_reader = TRUE]
                            /\ upread_guard' = next_waiter[1]
                            /\ UNCHANGED <<write_guard, being_upgraded>>
                       [] OTHER -> UNCHANGED <<write_guard, upread_guard, being_upgraded>>
                  ELSE UNCHANGED <<write_guard, upread_guard, being_upgraded>>
       ELSE UNCHANGED <<wait_queue, write_guard, upread_guard, being_upgraded>>

ReleaseWrite(t) ==
    /\ write_guard = t
    /\ lock_state' = [lock_state EXCEPT !.writer = FALSE]
    /\ write_guard' = NULL
    /\ LET wake_all_waiters == {i \in 1..Len(wait_queue) : 
                                LET waiter == wait_queue[i]
                                IN CASE waiter[2] = "read" -> CanAcquireRead
                                   [] waiter[2] = "write" -> CanAcquireWrite
                                   [] waiter[2] = "upread" -> CanAcquireUpread
                                   [] OTHER -> FALSE}
       IN IF wake_all_waiters # {}
          THEN /\ wait_queue' = SelectSeq(wait_queue, LAMBDA i: i \notin wake_all_waiters)
               /\ LET readers_to_wake == {wait_queue[i][1] : i \in wake_all_waiters /\ wait_queue[i][2] = "read"}
                      writer_to_wake == IF \E i \in wake_all_waiters : wait_queue[i][2] = "write"
                                       THEN CHOOSE i \in wake_all_waiters : wait_queue[i][2] = "write"
                                       ELSE NULL
                      upread_to_wake == IF \E i \in wake_all_waiters : wait_queue[i][2] = "upread"
                                       THEN CHOOSE i \in wake_all_waiters : wait_queue[i][2] = "upread"
                                       ELSE NULL
                  IN /\ read_guards' = read_guards \cup readers_to_wake
                     /\ lock_state' = [lock_state' EXCEPT !.reader_count = @ + Cardinality(readers_to_wake)]
                     /\ IF writer_to_wake # NULL
                        THEN /\ write_guard' = wait_queue[writer_to_wake][1]
                             /\ lock_state' = [lock_state' EXCEPT !.writer = TRUE]
                        ELSE UNCHANGED write_guard'
                     /\ IF upread_to_wake # NULL
                        THEN /\ upread_guard' = wait_queue[upread_to_wake][1]
                             /\ lock_state' = [lock_state' EXCEPT !.upgradeable_reader = TRUE]
                        ELSE UNCHANGED upread_guard'
          ELSE UNCHANGED <<wait_queue, read_guards, upread_guard>>
    /\ UNCHANGED being_upgraded

ReleaseUpread(t) ==
    /\ upread_guard = t
    /\ lock_state' = [lock_state EXCEPT !.upgradeable_reader = FALSE]
    /\ upread_guard' = NULL
    /\ being_upgraded' = FALSE
    /\ LET wake_all_waiters == {i \in 1..Len(wait_queue) : 
                                LET waiter == wait_queue[i]
                                IN CASE waiter[2] = "read" -> CanAcquireRead
                                   [] waiter[2] = "write" -> CanAcquireWrite
                                   [] waiter[2] = "upread" -> CanAcquireUpread
                                   [] OTHER -> FALSE}
       IN IF wake_all_waiters # {}
          THEN /\ wait_queue' = SelectSeq(wait_queue, LAMBDA i: i \notin wake_all_waiters)
               /\ LET readers_to_wake == {wait_queue[i][1] : i \in wake_all_waiters /\ wait_queue[i][2] = "read"}
                      writer_to_wake == IF \E i \in wake_all_waiters : wait_queue[i][2] = "write"
                                       THEN CHOOSE i \in wake_all_waiters : wait_queue[i][2] = "write"
                                       ELSE NULL
                      new_upread_to_wake == IF \E i \in wake_all_waiters : wait_queue[i][2] = "upread"
                                           THEN CHOOSE i \in wake_all_waiters : wait_queue[i][2] = "upread"
                                           ELSE NULL
                  IN /\ read_guards' = read_guards \cup readers_to_wake
                     /\ lock_state' = [lock_state' EXCEPT !.reader_count = @ + Cardinality(readers_to_wake)]
                     /\ IF writer_to_wake # NULL
                        THEN /\ write_guard' = wait_queue[writer_to_wake][1]
                             /\ lock_state' = [lock_state' EXCEPT !.writer = TRUE]
                        ELSE UNCHANGED write_guard
                     /\ IF new_upread_to_wake # NULL
                        THEN /\ upread_guard' = wait_queue[new_upread_to_wake][1]
                             /\ lock_state' = [lock_state' EXCEPT !.upgradeable_reader = TRUE]
                        ELSE UNCHANGED upread_guard'
          ELSE UNCHANGED <<wait_queue, read_guards, write_guard>>

StartUpgrade(t) ==
    /\ upread_guard = t
    /\ ~being_upgraded
    /\ being_upgraded' = TRUE
    /\ UNCHANGED <<lock_state, wait_queue, read_guards, write_guard, upread_guard>>

CompleteUpgrade(t) ==
    /\ upread_guard = t
    /\ being_upgraded
    /\ lock_state.reader_count = 0
    /\ lock_state' = [lock_state EXCEPT !.writer = TRUE, !.upgradeable_reader = FALSE]
    /\ write_guard' = t
    /\ upread_guard' = NULL
    /\ being_upgraded' = FALSE
    /\ UNCHANGED <<wait_queue, read_guards>>

Downgrade(t) ==
    /\ write_guard = t
    /\ lock_state' = [lock_state EXCEPT !.writer = FALSE, !.upgradeable_reader = TRUE]
    /\ write_guard' = NULL
    /\ upread_guard' = t
    /\ UNCHANGED <<wait_queue, read_guards, being_upgraded>>

Next ==
    \/ \E t \in Threads : TryRead(t)
    \/ \E t \in Threads : TryWrite(t)
    \/ \E t \in Threads : TryUpread(t)
    \/ \E t \in Threads : EnqueueRead(t)
    \/ \E t \in Threads : EnqueueWrite(t)
    \/ \E t \in Threads : EnqueueUpread(t)
    \/ \E t \in Threads : ReleaseRead(t)
    \/ \E t \in Threads : ReleaseWrite(t)
    \/ \E t \in Threads : ReleaseUpread(t)
    \/ \E t \in Threads : StartUpgrade(t)
    \/ \E t \in Threads : CompleteUpgrade(t)
    \/ \E t \in Threads : Downgrade(t)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

====