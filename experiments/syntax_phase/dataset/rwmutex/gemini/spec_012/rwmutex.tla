---- MODULE rwmutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Threads

VARIABLES writer, upreader, upgrading, readers, wait_queue, pc

vars == <<writer, upreader, upgrading, readers, wait_queue, pc>>

LockTypes == {"read", "write", "upread"}
PCValues == {"idle", "waiting", "holding_read", "holding_write", "holding_upread", "upgrading"}

TypeOK ==
    /\ writer \in Threads \cup {None}
    /\ upreader \in Threads \cup {None}
    /\ upgrading \in BOOLEAN
    /\ readers \subseteq Threads
    /\ wait_queue \in Seq(Threads \times LockTypes)
    /\ pc \in [Threads -> PCValues]

Init ==
    /\ writer = None
    /\ upreader = None
    /\ upgrading = FALSE
    /\ readers = {}
    /\ wait_queue = << >>
    /\ pc = [t \in Threads |-> "idle"]

CanRead == writer = None /\ \neg upgrading
CanWrite == writer = None /\ upreader = None /\ readers = {}
CanUpread == writer = None /\ upreader = None

Request(t, type) ==
    /\ pc[t] = "idle"
    /\ IF type = "read" THEN
        (IF CanRead THEN
            (/\ pc' = [pc EXCEPT ![t] = "holding_read"]
            /\ readers' = readers \cup {t}
            /\ UNCHANGED <<writer, upreader, upgrading, wait_queue>>)
        ELSE
            (/\ pc' = [pc EXCEPT ![t] = "waiting"]
            /\ wait_queue' = Append(wait_queue, <<t, "read">>)
            /\ UNCHANGED <<writer, upreader, upgrading, readers>>))
    ELSE (IF type = "write" THEN
        (IF CanWrite THEN
            (/\ pc' = [pc EXCEPT ![t] = "holding_write"]
            /\ writer' = t
            /\ UNCHANGED <<upreader, upgrading, readers, wait_queue>>)
        ELSE
            (/\ pc' = [pc EXCEPT ![t] = "waiting"]
            /\ wait_queue' = Append(wait_queue, <<t, "write">>)
            /\ UNCHANGED <<writer, upreader, upgrading, readers>>))
    ELSE (* type = "upread" *)
        (IF CanUpread THEN
            (/\ pc' = [pc EXCEPT ![t] = "holding_upread"]
            /\ upreader' = t
            /\ UNCHANGED <<writer, upgrading, readers, wait_queue>>)
        ELSE
            (/\ pc' = [pc EXCEPT ![t] = "waiting"]
            /\ wait_queue' = Append(wait_queue, <<t, "upread">>)
            /\ UNCHANGED <<writer, upreader, upgrading, readers>>)))

ReleaseRead(t) ==
    /\ pc[t] = "holding_read"
    /\ pc' = [pc EXCEPT ![t] = "idle"]
    /\ readers' = readers \setminus {t}
    /\ UNCHANGED <<writer, upreader, upgrading, wait_queue>>

ReleaseWrite(t) ==
    /\ pc[t] = "holding_write"
    /\ pc' = [pc EXCEPT ![t] = "idle"]
    /\ writer' = None
    /\ UNCHANGED <<upreader, upgrading, readers, wait_queue>>

ReleaseUpread(t) ==
    /\ pc[t] = "holding_upread"
    /\ pc' = [pc EXCEPT ![t] = "idle"]
    /\ upreader' = None
    /\ UNCHANGED <<writer, upgrading, readers, wait_queue>>

GrantLockFromQueue ==
    /\ Len(wait_queue) > 0
    /\ LET req == Head(wait_queue)
    /\ LET t == req[1]
    /\ LET type == req[2]
    /\ \/ (/\ type = "write"
           /\ CanWrite
           /\ writer' = t
           /\ pc' = [pc EXCEPT ![t] = "holding_write"]
           /\ wait_queue' = Tail(wait_queue)
           /\ UNCHANGED <<upreader, upgrading, readers>>)
       \/ (/\ type = "upread"
           /\ CanUpread
           /\ upreader' = t
           /\ pc' = [pc EXCEPT ![t] = "holding_upread"]
           /\ wait_queue' = Tail(wait_queue)
           /\ UNCHANGED <<writer, upgrading, readers>>)
       \/ (/\ type = "read"
           /\ CanRead
           /\ readers' = readers \cup {t}
           /\ pc' = [pc EXCEPT ![t] = "holding_read"]
           /\ wait_queue' = Tail(wait_queue)
           /\ UNCHANGED <<writer, upreader, upgrading>>)

StartUpgrade(t) ==
    /\ pc[t] = "holding_upread"
    /\ pc' = [pc EXCEPT ![t] = "upgrading"]
    /\ upgrading' = TRUE
    /\ UNCHANGED <<writer, upreader, readers, wait_queue>>

CompleteUpgrade(t) ==
    /\ pc[t] = "upgrading"
    /\ readers = {}
    /\ pc' = [pc EXCEPT ![t] = "holding_write"]
    /\ writer' = t
    /\ upreader' = None
    /\ upgrading' = FALSE
    /\ UNCHANGED <<readers, wait_queue>>

Downgrade(t) ==
    /\ pc[t] = "holding_write"
    /\ pc' = [pc EXCEPT ![t] = "holding_upread"]
    /\ writer' = None
    /\ upreader' = t
    /\ UNCHANGED <<upgrading, readers, wait_queue>>

Next ==
    \/ \E t \in Threads, type \in LockTypes : Request(t, type)
    \/ \E t \in Threads : ReleaseRead(t)
    \/ \E t \in Threads : ReleaseWrite(t)
    \/ \E t \in Threads : ReleaseUpread(t)
    \/ GrantLockFromQueue
    \/ \E t \in Threads : StartUpgrade(t)
    \/ \E t \in Threads : CompleteUpgrade(t)
    \/ \E t \in Threads : Downgrade(t)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

====
