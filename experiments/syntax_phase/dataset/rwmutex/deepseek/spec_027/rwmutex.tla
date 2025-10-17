---- MODULE rwmutex ----
EXTENDS TLC, Sequences, Naturals, FiniteSets

CONSTANTS Threads

VARIABLES state, waitQueue, activeThreads

vars == <<state, waitQueue, activeThreads>>

StateType == [writer: BOOLEAN, upreader: BOOLEAN, being_upgraded: BOOLEAN, reader_count: Nat]

TypeOK == 
    /\ state \in StateType
    /\ waitQueue \in Seq(Threads)
    /\ activeThreads \in [Threads -> {"idle", "read", "write", "upread"}]

Init == 
    /\ state = [writer |-> FALSE, upreader |-> FALSE, being_upgraded |-> FALSE, reader_count |-> 0]
    /\ waitQueue = <<>>
    /\ activeThreads = [t \in Threads |-> "idle"]

CanRead(t) == 
    /\ activeThreads[t] = "idle"
    /\ ~state.writer
    /\ ~state.being_upgraded

CanWrite(t) == 
    /\ activeThreads[t] = "idle"
    /\ state.reader_count = 0
    /\ ~state.writer
    /\ ~state.upreader
    /\ ~state.being_upgraded

CanUpread(t) == 
    /\ activeThreads[t] = "idle"
    /\ ~state.writer
    /\ ~state.upreader

ReadAcquire(t) == 
    /\ CanRead(t)
    /\ state' = [state EXCEPT !.reader_count = @ + 1]
    /\ activeThreads' = [activeThreads EXCEPT ![t] = "read"]
    /\ UNCHANGED waitQueue

WriteAcquire(t) == 
    /\ CanWrite(t)
    /\ state' = [state EXCEPT !.writer = TRUE]
    /\ activeThreads' = [activeThreads EXCEPT ![t] = "write"]
    /\ UNCHANGED waitQueue

UpreadAcquire(t) == 
    /\ CanUpread(t)
    /\ state' = [state EXCEPT !.upreader = TRUE]
    /\ activeThreads' = [activeThreads EXCEPT ![t] = "upread"]
    /\ UNCHANGED waitQueue

Block(t, op) == 
    /\ activeThreads[t] = "idle"
    /\ ~CanRead(t) \/ ~CanWrite(t) \/ ~CanUpread(t)
    /\ waitQueue' = Append(waitQueue, t)
    /\ UNCHANGED <<state, activeThreads>>

ReadRelease(t) == 
    /\ activeThreads[t] = "read"
    /\ state' = [state EXCEPT !.reader_count = @ - 1]
    /\ activeThreads' = [activeThreads EXCEPT ![t] = "idle"]
    /\ IF state'.reader_count = 0 THEN 
           \E w \in Threads: 
               /\ w \in Range(waitQueue)
               /\ waitQueue' = Tail(waitQueue)
       ELSE 
           /\ UNCHANGED waitQueue

WriteRelease(t) == 
    /\ activeThreads[t] = "write"
    /\ state' = [state EXCEPT !.writer = FALSE]
    /\ activeThreads' = [activeThreads EXCEPT ![t] = "idle"]
    /\ waitQueue' = <<>>

UpreadRelease(t) == 
    /\ activeThreads[t] = "upread"
    /\ state' = [state EXCEPT !.upreader = FALSE]
    /\ activeThreads' = [activeThreads EXCEPT ![t] = "idle"]
    /\ waitQueue' = <<>>

Upgrade(t) == 
    /\ activeThreads[t] = "upread"
    /\ state' = [state EXCEPT !.being_upgraded = TRUE]
    /\ UNCHANGED <<activeThreads, waitQueue>>
    /\ \A u \in Threads: activeThreads[u] = "read" => state'.reader_count > 0

CompleteUpgrade(t) == 
    /\ activeThreads[t] = "upread"
    /\ state.being_upgraded
    /\ state.reader_count = 0
    /\ state' = [writer |-> TRUE, upreader |-> FALSE, being_upgraded |-> FALSE, reader_count |-> 0]
    /\ activeThreads' = [activeThreads EXCEPT ![t] = "write"]
    /\ UNCHANGED waitQueue

Downgrade(t) == 
    /\ activeThreads[t] = "write"
    /\ state' = [state EXCEPT !.writer = FALSE, !.upreader = TRUE]
    /\ activeThreads' = [activeThreads EXCEPT ![t] = "upread"]
    /\ UNCHANGED waitQueue

Next == 
    \/ \E t \in Threads: ReadAcquire(t)
    \/ \E t \in Threads: WriteAcquire(t)
    \/ \E t \in Threads: UpreadAcquire(t)
    \/ \E t \in Threads: Block(t, "read")
    \/ \E t \in Threads: Block(t, "write")
    \/ \E t \in Threads: Block(t, "upread")
    \/ \E t \in Threads: ReadRelease(t)
    \/ \E t \in Threads: WriteRelease(t)
    \/ \E t \in Threads: UpreadRelease(t)
    \/ \E t \in Threads: Upgrade(t)
    \/ \E t \in Threads: CompleteUpgrade(t)
    \/ \E t \in Threads: Downgrade(t)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

====