
---- MODULE rwmutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags
CONSTANTS Threads, NULL
VARIABLES lock, waitQueue, writerThread, upreaderThread, threadState

TypeOK == 
    lock \in [writer: BOOLEAN, upreader: BOOLEAN, being_upgraded: BOOLEAN, reader_count: Nat]
    /\ waitQueue \in Seq(Threads)
    /\ writerThread \in Threads \union {NULL}
    /\ upreaderThread \in Threads \union {NULL}
    /\ threadState \in [Threads -> {"idle", "waiting", "holding_read", "holding_write", "holding_upread", "upgrading"}]

Init == 
    lock = [writer |-> FALSE, upreader |-> FALSE, being_upgraded |-> FALSE, reader_count |-> 0]
    /\ waitQueue = <<>>
    /\ writerThread = NULL
    /\ upreaderThread = NULL
    /\ threadState = [t \in Threads |-> "idle"]

StartRead(t) == 
    /\ threadState[t] = "idle"
    /\ \/ /\ ~lock.writer /\ ~lock.being_upgraded
          /\ lock' = [lock EXCEPT !reader_count = lock.reader_count + 1]
          /\ threadState' = [threadState EXCEPT ![t] = "holding_read"]
          /\ UNCHANGED <<waitQueue, writerThread, upreaderThread>>
       \/ /\ lock.writer \/ lock.being_upgraded
          /\ threadState' = [threadState EXCEPT ![t] = "waiting"]
          /\ waitQueue' = Append(waitQueue, t)
          /\ UNCHANGED <<lock, writerThread, upreaderThread>>

StartWrite(t) == 
    /\ threadState[t] = "idle"
    /\ \/ /\ lock = [writer |-> FALSE, upreader |-> FALSE, being_upgraded |-> FALSE, reader_count |-> 0]
          /\ lock' = [lock EXCEPT !writer = TRUE]
          /\ writerThread' = t
          /\ threadState' = [threadState EXCEPT ![t] = "holding_write"]
          /\ UNCHANGED <<waitQueue, upreaderThread>>
       \/ /\ lock # [writer |-> FALSE, upreader |-> FALSE, being_upgraded |-> FALSE, reader_count |-> 0]
          /\ threadState' = [threadState EXCEPT ![t] = "waiting"]
          /\ waitQueue' = Append(waitQueue, t)
          /\ UNCHANGED <<lock, writerThread, upreaderThread>>

StartUpread(t) == 
    /\ threadState[t] = "idle"
    /\ \/ /\ ~lock.writer /\ ~lock.upreader
          /\ lock' = [lock EXCEPT !upreader = TRUE]
          /\ upreaderThread' = t
          /\ threadState' = [threadState EXCEPT ![t] = "holding_upread"]
          /\ UNCHANGED <<waitQueue, writerThread>>
       \/ /\ lock.writer \/ lock.upreader
          /\ threadState' = [threadState EXCEPT ![t] = "waiting"]
          /\ waitQueue' = Append(waitQueue, t)
          /\ UNCHANGED <<lock, writerThread, upreaderThread>>

ReleaseRead(t) == 
    /\ threadState[t] = "holding_read"
    /\ lock' = [lock EXCEPT !reader_count = lock.reader_count - 1]
    /\ \/ /\ lock.reader_count = 1
          /\ waitQueue # <<>>
          /\ LET t_wake == Head(waitQueue) IN
             waitQueue' = Tail(waitQueue)
             /\ threadState' = [threadState EXCEPT ![t] = "idle", ![t_wake] = "idle"]
          /\ UNCHANGED <<writerThread, upreaderThread>>
       \/ /\ lock.reader_count # 1
          /\ threadState' = [threadState EXCEPT ![t] = "idle"]
          /\ UNCHANGED <<waitQueue, writerThread, upreaderThread>>
    /\ UNCHANGED <<writerThread, upreaderThread>>

ReleaseWrite(t) == 
    /\ threadState[t] = "holding_write"
    /\ lock' = [lock EXCEPT !writer = FALSE]
    /\ writerThread' = NULL
    /\ LET WaitingSet == { tq \in Threads : threadState[tq] = "waiting" } IN
       threadState' = [threadState EXCEPT ![t] = "idle", \A tq \in WaitingSet: @ = "idle"]
    /\ waitQueue' = <<>>
    /\ UNCHANGED <<upreaderThread>>

ReleaseUpread(t) == 
    /\ threadState[t] = "holding_upread"
    /\ lock' = [lock EXCEPT !upreader = FALSE]
    /\ upreaderThread' = NULL
    /\ \/ /\ lock = [writer |-> FALSE, upreader |-> TRUE, being_upgraded |-> FALSE, reader_count |-> 0]
          /\ LET WaitingSet == { tq \in Threads : threadState[tq] = "waiting" } IN
             threadState' = [threadState EXCEPT ![t] = "idle", \A tq \in WaitingSet: @ = "idle"]
          /\ waitQueue' = <<>>
       \/ /\ ~(lock = [writer |-> FALSE, upreader |-> TRUE, being_upgraded |-> FALSE, reader_count |-> 0])
          /\ threadState' = [threadState EXCEPT ![t] = "idle"]
          /\ UNCHANGED <<waitQueue>>
    /\ UNCHANGED <<writerThread>>

BeginUpgrade(t) == 
    /\ threadState[t] = "holding_upread"
    /\ upreaderThread = t
    /\ ~lock.being_upgraded
    /\ lock' = [lock EXCEPT !being_upgraded = TRUE]
    /\ threadState' = [threadState EXCEPT ![t] = "upgrading"]
    /\ UNCHANGED <<waitQueue, writerThread, upreaderThread>>

CompleteUpgrade(t) == 
    /\ threadState[t] = "upgrading"
    /\ upreaderThread = t
    /\ lock = [writer |-> FALSE, upreader |-> TRUE, being_upgraded |-> TRUE, reader_count |-> 0]
    /\ lock' = [writer |-> TRUE, upreader |-> FALSE, being_upgraded |-> FALSE, reader_count |-> 0]
    /\ writerThread' = t
    /\ upreaderThread' = NULL
    /\ threadState' = [threadState EXCEPT ![t] = "holding_write"]
    /\ UNCHANGED <<waitQueue>>

Downgrade(t) == 
    /\ threadState[t] = "holding_write"
    /\ writerThread = t
    /\ lock = [writer |-> TRUE, upreader |-> FALSE, being_upgraded |-> FALSE, reader_count |-> 0]
    /\ lock' = [writer |-> FALSE, upreader |-> TRUE, being_upgraded |-> FALSE, reader_count |-> 0]
    /\ writerThread' = NULL
    /\ upreaderThread' = t
    /\ threadState' = [threadState EXCEPT ![t] = "holding_upread"]
    /\ UNCHANGED <<waitQueue>>

Next == 
    \E t \in Threads: 
        StartRead(t) \/ StartWrite(t) \/ StartUpread(t) \/
        ReleaseRead(t) \/ ReleaseWrite(t) \/ ReleaseUpread(t) \/
        BeginUpgrade(t) \/ CompleteUpgrade(t) \/ Downgrade(t)

Vars == << lock, waitQueue, writerThread, upreaderThread, threadState >>
Spec == Init /\ [][Next]_Vars /\ WF_Vars(Next)
====