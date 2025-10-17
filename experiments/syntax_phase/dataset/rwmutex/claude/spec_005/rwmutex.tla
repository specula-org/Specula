---- MODULE rwmutex ----

EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Threads

VARIABLES
    lock_state,
    wait_queue,
    reader_guards,
    writer_guard,
    upread_guard

vars == <<lock_state, wait_queue, reader_guards, writer_guard, upread_guard>>

WRITER_BIT == 1
UPGRADEABLE_READER_BIT == 2
BEING_UPGRADED_BIT == 4
READER_COUNT_MASK == 8

TypeOK ==
    /\ lock_state \in [writer: BOOLEAN, upgradeable_reader: BOOLEAN, being_upgraded: BOOLEAN, reader_count: Nat]
    /\ wait_queue \in Seq(Threads)
    /\ reader_guards \subseteq Threads
    /\ writer_guard \in UNION {Threads, {{}}}
    /\ upread_guard \in UNION {Threads, {{}}}

Init ==
    /\ lock_state = [writer |-> FALSE, upgradeable_reader |-> FALSE, being_upgraded |-> FALSE, reader_count |-> 0]
    /\ wait_queue = <<>>
    /\ reader_guards = {}
    /\ writer_guard = {}
    /\ upread_guard = {}

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

CanUpgrade ==
    /\ lock_state.upgradeable_reader
    /\ lock_state.being_upgraded
    /\ lock_state.reader_count = 0

TryRead(t) ==
    /\ t \notin reader_guards
    /\ writer_guard = {}
    /\ upread_guard # t
    /\ CanAcquireRead
    /\ lock_state' = [lock_state EXCEPT !.reader_count = @ + 1]
    /\ reader_guards' = reader_guards \union {t}
    /\ UNCHANGED <<wait_queue, writer_guard, upread_guard>>

TryWrite(t) ==
    /\ writer_guard = {}
    /\ t \notin reader_guards
    /\ upread_guard # t
    /\ CanAcquireWrite
    /\ lock_state' = [lock_state EXCEPT !.writer = TRUE]
    /\ writer_guard' = t
    /\ UNCHANGED <<wait_queue, reader_guards, upread_guard>>

TryUpread(t) ==
    /\ upread_guard = {}
    /\ t \notin reader_guards
    /\ writer_guard # t
    /\ CanAcquireUpread
    /\ lock_state' = [lock_state EXCEPT !.upgradeable_reader = TRUE]
    /\ upread_guard' = t
    /\ UNCHANGED <<wait_queue, reader_guards, writer_guard>>

Read(t) ==
    \/ TryRead(t)
    \/ (/\ ~CanAcquireRead
        /\ wait_queue' = Append(wait_queue, t)
        /\ UNCHANGED <<lock_state, reader_guards, writer_guard, upread_guard>>)

Write(t) ==
    \/ TryWrite(t)
    \/ (/\ ~CanAcquireWrite
        /\ wait_queue' = Append(wait_queue, t)
        /\ UNCHANGED <<lock_state, reader_guards, writer_guard, upread_guard>>)

Upread(t) ==
    \/ TryUpread(t)
    \/ (/\ ~CanAcquireUpread
        /\ wait_queue' = Append(wait_queue, t)
        /\ UNCHANGED <<lock_state, reader_guards, writer_guard, upread_guard>>)

ReleaseRead(t) ==
    /\ t \in reader_guards
    /\ lock_state' = [lock_state EXCEPT !.reader_count = @ - 1]
    /\ reader_guards' = reader_guards \ {t}
    /\ IF lock_state'.reader_count = 0 /\ wait_queue # <<>>
       THEN wait_queue' = Tail(wait_queue)
       ELSE UNCHANGED wait_queue
    /\ UNCHANGED <<writer_guard, upread_guard>>

ReleaseWrite(t) ==
    /\ writer_guard = t
    /\ lock_state' = [lock_state EXCEPT !.writer = FALSE]
    /\ writer_guard' = {}
    /\ wait_queue' = <<>>
    /\ UNCHANGED <<reader_guards, upread_guard>>

ReleaseUpread(t) ==
    /\ upread_guard = t
    /\ lock_state' = [lock_state EXCEPT !.upgradeable_reader = FALSE, !.being_upgraded = FALSE]
    /\ upread_guard' = {}
    /\ wait_queue' = <<>>
    /\ UNCHANGED <<reader_guards, writer_guard>>

StartUpgrade(t) ==
    /\ upread_guard = t
    /\ ~lock_state.being_upgraded
    /\ lock_state' = [lock_state EXCEPT !.being_upgraded = TRUE]
    /\ UNCHANGED <<wait_queue, reader_guards, writer_guard, upread_guard>>

CompleteUpgrade(t) ==
    /\ upread_guard = t
    /\ CanUpgrade
    /\ lock_state' = [lock_state EXCEPT !.writer = TRUE, !.upgradeable_reader = FALSE, !.being_upgraded = FALSE]
    /\ writer_guard' = t
    /\ upread_guard' = {}
    /\ UNCHANGED <<wait_queue, reader_guards>>

Downgrade(t) ==
    /\ writer_guard = t
    /\ lock_state' = [lock_state EXCEPT !.writer = FALSE, !.upgradeable_reader = TRUE]
    /\ writer_guard' = {}
    /\ upread_guard' = t
    /\ UNCHANGED <<wait_queue, reader_guards>>

ProcessWaitQueue ==
    /\ wait_queue # <<>>
    /\ LET next_thread == Head(wait_queue)
       IN \/ (/\ CanAcquireRead
              /\ TryRead(next_thread)
              /\ wait_queue' = Tail(wait_queue))
          \/ (/\ CanAcquireWrite
              /\ TryWrite(next_thread)
              /\ wait_queue' = Tail(wait_queue))
          \/ (/\ CanAcquireUpread
              /\ TryUpread(next_thread)
              /\ wait_queue' = Tail(wait_queue))
          \/ UNCHANGED vars

Next ==
    \/ \E t \in Threads: Read(t)
    \/ \E t \in Threads: Write(t)
    \/ \E t \in Threads: Upread(t)
    \/ \E t \in Threads: ReleaseRead(t)
    \/ \E t \in Threads: ReleaseWrite(t)
    \/ \E t \in Threads: ReleaseUpread(t)
    \/ \E t \in Threads: StartUpgrade(t)
    \/ \E t \in Threads: CompleteUpgrade(t)
    \/ \E t \in Threads: Downgrade(t)
    \/ ProcessWaitQueue

Spec == Init /\ [][Next]_vars
        /\ \A t \in Threads: WF_vars(ReleaseRead(t))
        /\ \A t \in Threads: WF_vars(ReleaseWrite(t))
        /\ \A t \in Threads: WF_vars(ReleaseUpread(t))
        /\ \A t \in Threads: WF_vars(CompleteUpgrade(t))
        /\ WF_vars(ProcessWaitQueue)

====