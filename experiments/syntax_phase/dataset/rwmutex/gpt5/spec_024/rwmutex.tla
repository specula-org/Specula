---- MODULE rwmutex ----
EXTENDS TLC, Sequences, Naturals, FiniteSets

CONSTANTS Threads

VARIABLES
    Writer,
    Upread,
    BeingUpgraded,
    Readers,
    Q,
    ReadyR,
    ReadyW,
    ReadyU,
    Held

vars == <<Writer, Upread, BeingUpgraded, Readers, Q, ReadyR, ReadyW, ReadyU, Held>>

Kinds == {"Read", "Write", "Upread"}
HoldStates == {"None"} \cup Kinds

Request == [tid: Threads, kind: Kinds]

InQ(t) == \E i \in 1..Len(Q): Q[i].tid = t

Init ==
    /\ Writer = FALSE
    /\ Upread = FALSE
    /\ BeingUpgraded = FALSE
    /\ Readers = 0
    /\ Q = <<>>
    /\ ReadyR = {}
    /\ ReadyW = {}
    /\ ReadyU = {}
    /\ Held = [t \in Threads |-> "None"]

ReadAcquireDirect(t) ==
    /\ t \in Threads
    /\ Held[t] = "None"
    /\ ~InQ(t)
    /\ ~(t \in ReadyR \cup ReadyW \cup ReadyU)
    /\ Writer = FALSE
    /\ BeingUpgraded = FALSE
    /\ Readers' = Readers + 1
    /\ Held' = [Held EXCEPT ![t] = "Read"]
    /\ UNCHANGED <<Writer, Upread, BeingUpgraded, Q, ReadyR, ReadyW, ReadyU>>

WriteAcquireDirect(t) ==
    /\ t \in Threads
    /\ Held[t] = "None"
    /\ ~InQ(t)
    /\ ~(t \in ReadyR \cup ReadyW \cup ReadyU)
    /\ Writer = FALSE
    /\ Readers = 0
    /\ Upread = FALSE
    /\ Writer' = TRUE
    /\ Held' = [Held EXCEPT ![t] = "Write"]
    /\ UNCHANGED <<Upread, BeingUpgraded, Readers, Q, ReadyR, ReadyW, ReadyU>>

UpreadAcquireDirect(t) ==
    /\ t \in Threads
    /\ Held[t] = "None"
    /\ ~InQ(t)
    /\ ~(t \in ReadyR \cup ReadyW \cup ReadyU)
    /\ Writer = FALSE
    /\ Upread = FALSE
    /\ Upread' = TRUE
    /\ Held' = [Held EXCEPT ![t] = "Upread"]
    /\ UNCHANGED <<Writer, BeingUpgraded, Readers, Q, ReadyR, ReadyW, ReadyU>>

EnqueueRead(t) ==
    /\ t \in Threads
    /\ Held[t] = "None"
    /\ ~InQ(t)
    /\ ~(t \in ReadyR \cup ReadyW \cup ReadyU)
    /\ ~(Writer = FALSE /\ BeingUpgraded = FALSE)
    /\ Q' = Append(Q, [tid |-> t, kind |-> "Read"])
    /\ UNCHANGED <<Writer, Upread, BeingUpgraded, Readers, ReadyR, ReadyW, ReadyU, Held>>

EnqueueWrite(t) ==
    /\ t \in Threads
    /\ Held[t] = "None"
    /\ ~InQ(t)
    /\ ~(t \in ReadyR \cup ReadyW \cup ReadyU)
    /\ ~(Writer = FALSE /\ Readers = 0 /\ Upread = FALSE)
    /\ Q' = Append(Q, [tid |-> t, kind |-> "Write"])
    /\ UNCHANGED <<Writer, Upread, BeingUpgraded, Readers, ReadyR, ReadyW, ReadyU, Held>>

EnqueueUpread(t) ==
    /\ t \in Threads
    /\ Held[t] = "None"
    /\ ~InQ(t)
    /\ ~(t \in ReadyR \cup ReadyW \cup ReadyU)
    /\ ~(Writer = FALSE /\ Upread = FALSE)
    /\ Q' = Append(Q, [tid |-> t, kind |-> "Upread"])
    /\ UNCHANGED <<Writer, Upread, BeingUpgraded, Readers, ReadyR, ReadyW, ReadyU, Held>>

ReadAcquireReady(t) ==
    /\ t \in Threads
    /\ t \in ReadyR
    /\ Held[t] = "None"
    /\ Writer = FALSE
    /\ BeingUpgraded = FALSE
    /\ Readers' = Readers + 1
    /\ ReadyR' = ReadyR \ {t}
    /\ Held' = [Held EXCEPT ![t] = "Read"]
    /\ UNCHANGED <<Writer, Upread, BeingUpgraded, Q, ReadyW, ReadyU>>

WriteAcquireReady(t) ==
    /\ t \in Threads
    /\ t \in ReadyW
    /\ Held[t] = "None"
    /\ Writer = FALSE
    /\ Readers = 0
    /\ Upread = FALSE
    /\ Writer' = TRUE
    /\ ReadyW' = ReadyW \ {t}
    /\ Held' = [Held EXCEPT ![t] = "Write"]
    /\ UNCHANGED <<Upread, BeingUpgraded, Readers, Q, ReadyR, ReadyU>>

UpreadAcquireReady(t) ==
    /\ t \in Threads
    /\ t \in ReadyU
    /\ Held[t] = "None"
    /\ Writer = FALSE
    /\ Upread = FALSE
    /\ Upread' = TRUE
    /\ ReadyU' = ReadyU \ {t}
    /\ Held' = [Held EXCEPT ![t] = "Upread"]
    /\ UNCHANGED <<Writer, BeingUpgraded, Readers, Q, ReadyR, ReadyW>>

ReadRelease(t) ==
    /\ t \in Threads
    /\ Held[t] = "Read"
    /\ Readers' = Readers - 1
    /\ Held' = [Held EXCEPT ![t] = "None"]
    /\ IF Readers' = 0 /\ Len(Q) > 0 THEN
          LET r == Q[1] IN
            /\ Q' = SubSeq(Q, 2, Len(Q))
            /\ ReadyR' = IF r.kind = "Read" THEN ReadyR \cup {r.tid} ELSE ReadyR
            /\ ReadyW' = IF r.kind = "Write" THEN ReadyW \cup {r.tid} ELSE ReadyW
            /\ ReadyU' = IF r.kind = "Upread" THEN ReadyU \cup {r.tid} ELSE ReadyU
       ELSE
            /\ Q' = Q
            /\ ReadyR' = ReadyR
            /\ ReadyW' = ReadyW
            /\ ReadyU' = ReadyU
    /\ UNCHANGED <<Writer, Upread, BeingUpgraded>>

WriteRelease(t) ==
    /\ t \in Threads
    /\ Held[t] = "Write"
    /\ Writer' = FALSE
    /\ Held' = [Held EXCEPT ![t] = "None"]
    /\ LET Rset == { Q[i].tid : i \in 1..Len(Q) /\ Q[i].kind = "Read" } IN
       LET Wset == { Q[i].tid : i \in 1..Len(Q) /\ Q[i].kind = "Write" } IN
       LET Uset == { Q[i].tid : i \in 1..Len(Q) /\ Q[i].kind = "Upread" } IN
          /\ Q' = <<>>
          /\ ReadyR' = ReadyR \cup Rset
          /\ ReadyW' = ReadyW \cup Wset
          /\ ReadyU' = ReadyU \cup Uset
    /\ UNCHANGED <<Upread, BeingUpgraded, Readers>>

UpreadRelease(t) ==
    /\ t \in Threads
    /\ Held[t] = "Upread"
    /\ Upread' = FALSE
    /\ Held' = [Held EXCEPT ![t] = "None"]
    /\ IF Readers = 0 THEN
          LET Rset == { Q[i].tid : i \in 1..Len(Q) /\ Q[i].kind = "Read" } IN
          LET Wset == { Q[i].tid : i \in 1..Len(Q) /\ Q[i].kind = "Write" } IN
          LET Uset == { Q[i].tid : i \in 1..Len(Q) /\ Q[i].kind = "Upread" } IN
            /\ Q' = <<>>
            /\ ReadyR' = ReadyR \cup Rset
            /\ ReadyW' = ReadyW \cup Wset
            /\ ReadyU' = ReadyU \cup Uset
       ELSE
            /\ Q' = Q
            /\ ReadyR' = ReadyR
            /\ ReadyW' = ReadyW
            /\ ReadyU' = ReadyU
    /\ UNCHANGED <<Writer, BeingUpgraded, Readers>>

UpgradeStart(t) ==
    /\ t \in Threads
    /\ Held[t] = "Upread"
    /\ Writer = FALSE
    /\ BeingUpgraded = FALSE
    /\ BeingUpgraded' = TRUE
    /\ UNCHANGED <<Writer, Upread, Readers, Q, ReadyR, ReadyW, ReadyU, Held>>

UpgradeComplete(t) ==
    /\ t \in Threads
    /\ Held[t] = "Upread"
    /\ BeingUpgraded = TRUE
    /\ Readers = 0
    /\ Writer = FALSE
    /\ Writer' = TRUE
    /\ BeingUpgraded' = FALSE
    /\ Held' = [Held EXCEPT ![t] = "Write"]
    /\ UNCHANGED <<Upread, Readers, Q, ReadyR, ReadyW, ReadyU>>

Downgrade(t) ==
    /\ t \in Threads
    /\ Held[t] = "Write"
    /\ Writer' = FALSE
    /\ Upread' = TRUE
    /\ Held' = [Held EXCEPT ![t] = "Upread"]
    /\ LET Rset == { Q[i].tid : i \in 1..Len(Q) /\ Q[i].kind = "Read" } IN
       LET Wset == { Q[i].tid : i \in 1..Len(Q) /\ Q[i].kind = "Write" } IN
       LET Uset == { Q[i].tid : i \in 1..Len(Q) /\ Q[i].kind = "Upread" } IN
          /\ Q' = <<>>
          /\ ReadyR' = ReadyR \cup Rset
          /\ ReadyW' = ReadyW \cup Wset
          /\ ReadyU' = ReadyU \cup Uset
    /\ UNCHANGED <<BeingUpgraded, Readers>>

Next ==
    \/ \E t \in Threads: ReadAcquireDirect(t)
    \/ \E t \in Threads: WriteAcquireDirect(t)
    \/ \E t \in Threads: UpreadAcquireDirect(t)
    \/ \E t \in Threads: EnqueueRead(t)
    \/ \E t \in Threads: EnqueueWrite(t)
    \/ \E t \in Threads: EnqueueUpread(t)
    \/ \E t \in Threads: ReadAcquireReady(t)
    \/ \E t \in Threads: WriteAcquireReady(t)
    \/ \E t \in Threads: UpreadAcquireReady(t)
    \/ \E t \in Threads: ReadRelease(t)
    \/ \E t \in Threads: WriteRelease(t)
    \/ \E t \in Threads: UpreadRelease(t)
    \/ \E t \in Threads: UpgradeStart(t)
    \/ \E t \in Threads: UpgradeComplete(t)
    \/ \E t \in Threads: Downgrade(t)

Spec ==
    Init /\ [][Next]_vars /\ WF_vars(Next)

====