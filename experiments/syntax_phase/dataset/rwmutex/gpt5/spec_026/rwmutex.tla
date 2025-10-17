---- MODULE rwmutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Threads

VARIABLES lock, Q, pc

Ops == {"read", "write", "upread"}
States == {"idle", "waitingRead", "reading", "waitingWrite", "writing", "waitingUpread", "upreading", "upgrading"}

TypeOK ==
    /\ lock \in [wr: BOOLEAN, ur: BOOLEAN, bu: BOOLEAN, rc: Nat]
    /\ Q \in Seq([t: Threads, op: Ops])
    /\ \A i, j \in 1..Len(Q): i # j => Q[i].t # Q[j].t
    /\ pc \in [Threads -> States]

Init ==
    /\ lock = [wr |-> FALSE, ur |-> FALSE, bu |-> FALSE, rc |-> 0]
    /\ Q = << >>
    /\ pc \in [Threads -> {"idle"}]

InQ(t) == \E i \in 1..Len(Q): Q[i].t = t

RECURSIVE FRLen(_)
FRLen(q) ==
    IF Len(q) = 0 THEN 0
    ELSE IF q[1].op = "read" THEN 1 + FRLen(SubSeq(q, 2, Len(q)))
    ELSE 0

Admitted(q) ==
    IF Len(q) = 0 THEN {}
    ELSE IF q[1].op = "read" THEN { q[i].t : i \in 1..FRLen(q) }
    ELSE { q[1].t }

Remove(q, t) ==
    LET i == CHOOSE j \in 1..Len(q): q[j].t = t
    IN SubSeq(q, 1, i-1) \o SubSeq(q, i+1, Len(q))

TryReadOK == ~lock.wr /\ ~lock.bu
TryWriteOK == (lock.rc = 0) /\ ~lock.wr /\ ~lock.ur /\ ~lock.bu
TryUpreadOK == ~lock.wr /\ ~lock.ur

Read(t) ==
    /\ pc[t] = "idle"
    /\ IF (Len(Q) = 0 /\ TryReadOK)
       THEN /\ lock' = [lock EXCEPT !.rc = @ + 1]
            /\ pc' = [pc EXCEPT ![t] = "reading"]
            /\ Q' = Q
       ELSE /\ ~InQ(t)
            /\ Q' = Append(Q, [t |-> t, op |-> "read"])
            /\ pc' = [pc EXCEPT ![t] = "waitingRead"]
            /\ lock' = lock

ReadAcquireFromQueue(t) ==
    /\ pc[t] = "waitingRead"
    /\ t \in Admitted(Q)
    /\ TryReadOK
    /\ Q' = Remove(Q, t)
    /\ lock' = [lock EXCEPT !.rc = @ + 1]
    /\ pc' = [pc EXCEPT ![t] = "reading"]

ReadRelease(t) ==
    /\ pc[t] = "reading"
    /\ lock.rc > 0
    /\ lock' = [lock EXCEPT !.rc = @ - 1]
    /\ pc' = [pc EXCEPT ![t] = "idle"]
    /\ Q' = Q

Write(t) ==
    /\ pc[t] = "idle"
    /\ IF (Len(Q) = 0 /\ TryWriteOK)
       THEN /\ lock' = [lock EXCEPT !.wr = TRUE]
            /\ pc' = [pc EXCEPT ![t] = "writing"]
            /\ Q' = Q
       ELSE /\ ~InQ(t)
            /\ Q' = Append(Q, [t |-> t, op |-> "write"])
            /\ pc' = [pc EXCEPT ![t] = "waitingWrite"]
            /\ lock' = lock

WriteAcquireFromQueue(t) ==
    /\ pc[t] = "waitingWrite"
    /\ t \in Admitted(Q)
    /\ TryWriteOK
    /\ Q' = Remove(Q, t)
    /\ lock' = [lock EXCEPT !.wr = TRUE]
    /\ pc' = [pc EXCEPT ![t] = "writing"]

WriteRelease(t) ==
    /\ pc[t] = "writing"
    /\ lock.wr = TRUE
    /\ lock' = [lock EXCEPT !.wr = FALSE]
    /\ pc' = [pc EXCEPT ![t] = "idle"]
    /\ Q' = Q

Upread(t) ==
    /\ pc[t] = "idle"
    /\ IF (Len(Q) = 0 /\ TryUpreadOK)
       THEN /\ lock' = [lock EXCEPT !.ur = TRUE]
            /\ pc' = [pc EXCEPT ![t] = "upreading"]
            /\ Q' = Q
       ELSE /\ ~InQ(t)
            /\ Q' = Append(Q, [t |-> t, op |-> "upread"])
            /\ pc' = [pc EXCEPT ![t] = "waitingUpread"]
            /\ lock' = lock

UpreadAcquireFromQueue(t) ==
    /\ pc[t] = "waitingUpread"
    /\ t \in Admitted(Q)
    /\ TryUpreadOK
    /\ Q' = Remove(Q, t)
    /\ lock' = [lock EXCEPT !.ur = TRUE]
    /\ pc' = [pc EXCEPT ![t] = "upreading"]

UpreadRelease(t) ==
    /\ pc[t] = "upreading"
    /\ lock.ur = TRUE
    /\ lock' = [lock EXCEPT !.ur = FALSE]
    /\ pc' = [pc EXCEPT ![t] = "idle"]
    /\ Q' = Q

UpgradeStart(t) ==
    /\ pc[t] = "upreading"
    /\ lock.ur = TRUE
    /\ ~lock.bu
    /\ lock' = [lock EXCEPT !.bu = TRUE]
    /\ pc' = [pc EXCEPT ![t] = "upgrading"]
    /\ Q' = Q

TryUpgrade(t) ==
    /\ pc[t] = "upgrading"
    /\ lock.ur = TRUE
    /\ lock.bu = TRUE
    /\ ~lock.wr
    /\ lock.rc = 0
    /\ lock' = [lock EXCEPT !.wr = TRUE, !.bu = FALSE, !.ur = FALSE]
    /\ pc' = [pc EXCEPT ![t] = "writing"]
    /\ Q' = Q

Downgrade(t) ==
    /\ pc[t] = "writing"
    /\ lock.wr = TRUE
    /\ lock' = [lock EXCEPT !.wr = FALSE, !.ur = TRUE, !.bu = FALSE]
    /\ pc' = [pc EXCEPT ![t] = "upreading"]
    /\ Q' = Q

Next ==
    \E t \in Threads:
        \/ Read(t)
        \/ ReadAcquireFromQueue(t)
        \/ ReadRelease(t)
        \/ Write(t)
        \/ WriteAcquireFromQueue(t)
        \/ WriteRelease(t)
        \/ Upread(t)
        \/ UpreadAcquireFromQueue(t)
        \/ UpreadRelease(t)
        \/ UpgradeStart(t)
        \/ TryUpgrade(t)
        \/ Downgrade(t)

vars == << lock, Q, pc >>

Spec ==
    Init /\ [][Next]_vars /\
    (\A t \in Threads:
        WF_vars(ReadAcquireFromQueue(t)) /\
        WF_vars(WriteAcquireFromQueue(t)) /\
        WF_vars(UpreadAcquireFromQueue(t)) /\
        WF_vars(TryUpgrade(t))
    )

====