
---- MODULE rwmutex ----
EXTENDS TLC, Sequences, Naturals, FiniteSets

CONSTANTS Threads, MaxReaders
ASSUME MaxReaders > 0

VARIABLES lockState, waitQueue, threadState

State == [writer: {0,1}, upread: {0,1}, being_upgraded: {0,1}, readers: 0..MaxReaders]
ThreadStateType == [mode: {"idle"}] 
                   \cup [mode: {"waiting"}, op: {"read","write","upread"}]
                   \cup [mode: {"holding"}, op: {"read","write","upread"}]

TypeOK == 
    lockState \in State
    /\ waitQueue \in Seq(Threads)
    /\ threadState \in [Threads -> ThreadStateType]
    /\ \A t \in Threads: 
          (threadState[t].mode = "waiting") <=> (t \in Range(waitQueue))

Init == 
    lockState = [writer |-> 0, upread |-> 0, being_upgraded |-> 0, readers |-> 0]
    /\ waitQueue = << >>
    /\ threadState = [t \in Threads |-> [mode |-> "idle"]]

Read(t) == 
    LET thread == t IN
    /\ threadState[thread].mode = "idle"
    /\ IF lockState.writer = 0 /\ lockState.being_upgraded = 0 
        THEN 
            /\ lockState' = [lockState EXCEPT !.readers = lockState.readers + 1]
            /\ threadState' = [threadState EXCEPT ![thread] = [mode |-> "holding", op |-> "read"]]
            /\ waitQueue' = waitQueue
        ELSE
            /\ threadState' = [threadState EXCEPT ![thread] = [mode |-> "waiting", op |-> "read"]]
            /\ waitQueue' = Append(waitQueue, thread)
            /\ UNCHANGED <<lockState>>

Write(t) == 
    LET thread == t IN
    /\ threadState[thread].mode = "idle"
    /\ IF lockState.writer = 0 /\ lockState.upread = 0 /\ lockState.readers = 0 
        THEN 
            /\ lockState' = [lockState EXCEPT !.writer = 1]
            /\ threadState' = [threadState EXCEPT ![thread] = [mode |-> "holding", op |-> "write"]]
            /\ waitQueue' = waitQueue
        ELSE
            /\ threadState' = [threadState EXCEPT ![thread] = [mode |-> "waiting", op |-> "write"]]
            /\ waitQueue' = Append(waitQueue, thread)
            /\ UNCHANGED <<lockState>>

Upread(t) == 
    LET thread == t IN
    /\ threadState[thread].mode = "idle"
    /\ IF lockState.writer = 0 /\ lockState.upread = 0 
        THEN 
            /\ lockState' = [lockState EXCEPT !.upread = 1]
            /\ threadState' = [threadState EXCEPT ![thread] = [mode |-> "holding", op |-> "upread"]]
            /\ waitQueue' = waitQueue
        ELSE
            /\ threadState' = [threadState EXCEPT ![thread] = [mode |-> "waiting", op |-> "upread"]]
            /\ waitQueue' = Append(waitQueue, thread)
            /\ UNCHANGED <<lockState>>

Upgrade(t) == 
    LET thread == t IN
    /\ threadState[thread].mode = "holding" 
    /\ threadState[thread].op = "upread"
    /\ lockState.readers = 0
    /\ lockState' = [writer |-> 1, upread |-> 0, being_upgraded |-> 0, readers |-> 0]
    /\ threadState' = [threadState EXCEPT ![thread] = [mode |-> "holding", op |-> "write"]]
    /\ UNCHANGED <<waitQueue>>

Downgrade(t) == 
    LET thread == t IN
    /\ threadState[thread].mode = "holding" 
    /\ threadState[thread].op = "write"
    /\ lockState = [writer |-> 1, upread |-> 0, being_upgraded |-> 0, readers |-> 0]
    /\ lockState' = [writer |-> 0, upread |-> 1, being_upgraded |-> 0, readers |-> 0]
    /\ threadState' = [s \in Threads |-> 
                         IF s = thread THEN [mode |-> "holding", op |-> "upread"]
                         ELSE IF s \in Range(waitQueue) THEN [mode |-> "idle"]
                         ELSE threadState[s] ]
    /\ waitQueue' = << >>

ReleaseRead(t) == 
    LET thread == t IN
    /\ threadState[thread].mode = "holding" 
    /\ threadState[thread].op = "read"
    /\ lockState' = [lockState EXCEPT !.readers = lockState.readers - 1]
    /\ \/ /\ lockState'.readers = 0
          /\ waitQueue # << >>
          /\ LET t0 == Head(waitQueue) IN
             waitQueue' = Tail(waitQueue)
             /\ threadState' = [threadState EXCEPT ![thread] = [mode |-> "idle"], ![t0] = [mode |-> "idle"]]
       \/ /\ ~ (lockState'.readers = 0 /\ waitQueue # << >>)
          /\ threadState' = [threadState EXCEPT ![thread] = [mode |-> "idle"]]
          /\ waitQueue' = waitQueue

ReleaseWrite(t) == 
    LET thread == t IN
    /\ threadState[thread].mode = "holding" 
    /\ threadState[thread].op = "write"
    /\ lockState' = [lockState EXCEPT !.writer = 0]
    /\ waitQueue' = << >>
    /\ threadState' = [s \in Threads |-> 
                         IF s = thread THEN [mode |-> "idle"]
                         ELSE IF s \in Range(waitQueue) THEN [mode |-> "idle"]
                         ELSE threadState[s] ]

ReleaseUpread(t) == 
    LET thread == t IN
    /\ threadState[thread].mode = "holding" 
    /\ threadState[thread].op = "upread"
    /\ lockState' = [lockState EXCEPT !.upread = 0]
    /\ \/ /\ lockState = [writer |-> 0, upread |-> 1, being_upgraded |-> 0, readers |-> 0]
          /\ waitQueue' = << >>
          /\ threadState' = [s \in Threads |-> 
                         IF s = thread THEN [mode |-> "idle"]
                         ELSE IF s \in Range(waitQueue) THEN [mode |-> "idle"]
                         ELSE threadState[s] ]
       \/ /\ ~ (lockState = [writer |-> 0, upread |-> 1, being_upgraded |-> 0, readers |-> 0])
          /\ threadState' = [threadState EXCEPT ![thread] = [mode |-> "idle"]]
          /\ waitQueue' = waitQueue

Next == 
    \E t \in Threads: 
        Read(t) \/ Write(t) \/ Upread(t) \/ 
        Upgrade(t) \/ Downgrade(t) \/
        ReleaseRead(t) \/ ReleaseWrite(t) \/ ReleaseUpread(t)

Vars == <<lockState, waitQueue, threadState>>
WF_Vars(A) == WF_(Vars)(A)

Spec == 
    Init 
    /\ [][Next]_Vars 
    /\ WF_Vars(Next)

====