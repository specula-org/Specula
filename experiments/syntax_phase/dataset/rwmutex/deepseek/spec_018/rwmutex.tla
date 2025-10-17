---- MODULE rwmutex ----
EXTENDS TLC, Sequences, Naturals, FiniteSets
CONSTANT Threads
VARIABLES lock, queue
Vars == <<lock, queue>>
TypeOK == 
    /\ lock \in [writer: BOOLEAN, upread: BOOLEAN, being_upgraded: BOOLEAN, reader_count: Nat]
    /\ queue \in Seq(Threads)
Init == 
    /\ lock = [writer |-> FALSE, upread |-> FALSE, being_upgraded |-> FALSE, reader_count |-> 0]
    /\ queue = <<>>
CanRead == ~lock.writer /\ ~lock.being_upgraded
CanWrite == lock.reader_count = 0 /\ ~lock.writer /\ ~lock.upread
CanUpread == ~lock.writer /\ ~lock.upread
TryRead(t) == 
    /\ CanRead
    /\ lock' = [lock EXCEPT !.reader_count = lock.reader_count + 1]
    /\ UNCHANGED queue
TryWrite(t) == 
    /\ CanWrite
    /\ lock' = [lock EXCEPT !.writer = TRUE]
    /\ UNCHANGED queue
TryUpread(t) == 
    /\ CanUpread
    /\ lock' = [lock EXCEPT !.upread = TRUE]
    /\ UNCHANGED queue
BlockRead(t) == 
    /\ ~CanRead
    /\ queue' = Append(queue, t)
    /\ UNCHANGED lock
BlockWrite(t) == 
    /\ ~CanWrite
    /\ queue' = Append(queue, t)
    /\ UNCHANGED lock
BlockUpread(t) == 
    /\ ~CanUpread
    /\ queue' = Append(queue, t)
    /\ UNCHANGED lock
StartUpgrade(t) == 
    /\ lock.upread
    /\ ~lock.being_upgraded
    /\ lock' = [lock EXCEPT !.being_upgraded = TRUE]
    /\ UNCHANGED queue
CompleteUpgrade(t) == 
    /\ lock.being_upgraded
    /\ lock.reader_count = 0
    /\ lock' = [writer |-> TRUE, upread |-> FALSE, being_upgraded |-> FALSE, reader_count |-> 0]
    /\ UNCHANGED queue
Downgrade(t) == 
    /\ lock.writer
    /\ ~lock.upread
    /\ lock' = [writer |-> FALSE, upread |-> TRUE, being_upgraded |-> FALSE, reader_count |-> 0]
    /\ UNCHANGED queue
ReleaseRead(t) == 
    /\ lock.reader_count > 0
    /\ lock' = [lock EXCEPT !.reader_count = lock.reader_count - 1]
    /\ queue' = IF lock.reader_count = 1 /\ queue /= <<>> THEN Tail(queue) ELSE queue
ReleaseWrite(t) == 
    /\ lock.writer
    /\ lock' = [lock EXCEPT !.writer = FALSE]
    /\ queue' = IF lock.reader_count = 0 THEN <<>> ELSE queue
ReleaseUpread(t) == 
    /\ lock.upread
    /\ lock' = [lock EXCEPT !.upread = FALSE]
    /\ queue' = IF lock.writer = FALSE /\ lock.being_upgraded = FALSE /\ lock.reader_count = 0 THEN <<>> ELSE queue
Next == 
    \/ \E t \in Threads: TryRead(t)
    \/ \E t \in Threads: TryWrite(t)
    \/ \E t \in Threads: TryUpread(t)
    \/ \E t \in Threads: BlockRead(t)
    \/ \E t \in Threads: BlockWrite(t)
    \/ \E t \in Threads: BlockUpread(t)
    \/ \E t \in Threads: StartUpgrade(t)
    \/ \E t \in Threads: CompleteUpgrade(t)
    \/ \E t \in Threads: Downgrade(t)
    \/ \E t \in Threads: ReleaseRead(t)
    \/ \E t \in Threads: ReleaseWrite(t)
    \/ \E t \in Threads: ReleaseUpread(t)
WF_Vars(A) == WF_vars(A)
Spec == Init /\ [][Next]_Vars /\ WF_Vars(Next)
====