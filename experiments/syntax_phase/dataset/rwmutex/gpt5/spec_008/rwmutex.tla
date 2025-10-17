---- MODULE rwmutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANT THREADS

Kinds == {"Read", "Write", "Upread"}
States == {"Idle", "WaitRead", "WaitWrite", "WaitUpread", "Reading", "Writing", "Upreading", "Upgrading"}

Request == [tid: THREADS, kind: Kinds]

VARIABLES
    st,        \* st \in [THREADS -> States]
    lockW,     \* 0/1: WRITER bit
    lockU,     \* 0/1: UPGRADEABLE_READER bit
    lockB,     \* 0/1: BEING_UPGRADED bit
    readers,   \* Nat reader count
    queue,     \* Seq(Request)
    awoken     \* SUBSET THREADS

vars == << st, lockW, lockU, lockB, readers, queue, awoken >>

QueueEmpty == Len(queue) = 0
HeadReq == queue[1]
IsHead(t) == ~QueueEmpty /\ HeadReq.tid = t
Tail(q) == IF Len(q) = 0 THEN << >> ELSE SubSeq(q, 2, Len(q))

AllWaitingTids(q) ==
    { q[i].tid : i \in 1..Len(q) }

CanReadNow == lockW = 0 /\ lockB = 0
CanWriteNow == lockW = 0 /\ lockU = 0 /\ readers = 0 /\ lockB = 0
CanUpreadNow == lockW = 0 /\ lockU = 0

TypeOK ==
    /\ st \in [THREADS -> States]
    /\ lockW \in {0, 1}
    /\ lockU \in {0, 1}
    /\ lockB \in {0, 1}
    /\ readers \in Nat
    /\ queue \in Seq(Request)
    /\ awoken \subseteq THREADS

Init ==
    /\ st = [t \in THREADS |-> "Idle"]
    /\ lockW = 0
    /\ lockU = 0
    /\ lockB = 0
    /\ readers = 0
    /\ queue = << >>
    /\ awoken = {}

\* Call operations: immediate try if queue empty and condition holds; otherwise enqueue
CallReadAcquireNow(t) ==
    /\ st[t] = "Idle"
    /\ QueueEmpty
    /\ CanReadNow
    /\ st' = [st EXCEPT ![t] = "Reading"]
    /\ readers' = readers + 1
    /\ UNCHANGED << lockW, lockU, lockB, queue, awoken >>

CallReadEnqueue(t) ==
    /\ st[t] = "Idle"
    /\ ~(QueueEmpty /\ CanReadNow)
    /\ queue' = Append(queue, [tid |-> t, kind |-> "Read"])
    /\ st' = [st EXCEPT ![t] = "WaitRead"]
    /\ UNCHANGED << lockW, lockU, lockB, readers, awoken >>

CallWriteAcquireNow(t) ==
    /\ st[t] = "Idle"
    /\ QueueEmpty
    /\ CanWriteNow
    /\ st' = [st EXCEPT ![t] = "Writing"]
    /\ lockW' = 1
    /\ UNCHANGED << lockU, lockB, readers, queue, awoken >>

CallWriteEnqueue(t) ==
    /\ st[t] = "Idle"
    /\ ~(QueueEmpty /\ CanWriteNow)
    /\ queue' = Append(queue, [tid |-> t, kind |-> "Write"])
    /\ st' = [st EXCEPT ![t] = "WaitWrite"]
    /\ UNCHANGED << lockW, lockU, lockB, readers, awoken >>

CallUpreadAcquireNow(t) ==
    /\ st[t] = "Idle"
    /\ QueueEmpty
    /\ CanUpreadNow
    /\ st' = [st EXCEPT ![t] = "Upreading"]
    /\ lockU' = 1
    /\ UNCHANGED << lockW, lockB, readers, queue, awoken >>

CallUpreadEnqueue(t) ==
    /\ st[t] = "Idle"
    /\ ~(QueueEmpty /\ CanUpreadNow)
    /\ queue' = Append(queue, [tid |-> t, kind |-> "Upread"])
    /\ st' = [st EXCEPT ![t] = "WaitUpread"]
    /\ UNCHANGED << lockW, lockU, lockB, readers, awoken >>

\* Acquisitions from the FIFO wait queue; require wake_one/wake_all to have awoken the thread
AcquireFromQueueRead(t) ==
    /\ st[t] = "WaitRead"
    /\ IsHead(t)
    /\ t \in awoken
    /\ CanReadNow
    /\ st' = [st EXCEPT ![t] = "Reading"]
    /\ readers' = readers + 1
    /\ queue' = Tail(queue)
    /\ awoken' = awoken \ {t}
    /\ UNCHANGED << lockW, lockU, lockB >>

AcquireFromQueueWrite(t) ==
    /\ st[t] = "WaitWrite"
    /\ IsHead(t)
    /\ t \in awoken
    /\ CanWriteNow
    /\ st' = [st EXCEPT ![t] = "Writing"]
    /\ lockW' = 1
    /\ queue' = Tail(queue)
    /\ awoken' = awoken \ {t}
    /\ UNCHANGED << lockU, lockB, readers >>

AcquireFromQueueUpread(t) ==
    /\ st[t] = "WaitUpread"
    /\ IsHead(t)
    /\ t \in awoken
    /\ CanUpreadNow
    /\ st' = [st EXCEPT ![t] = "Upreading"]
    /\ lockU' = 1
    /\ queue' = Tail(queue)
    /\ awoken' = awoken \ {t}
    /\ UNCHANGED << lockW, lockB, readers >>

\* Release actions with wake strategies
ReleaseRead(t) ==
    /\ st[t] = "Reading"
    /\ readers > 0
    /\ st' = [st EXCEPT ![t] = "Idle"]
    /\ readers' = readers - 1
    /\ LET newAwoken ==
           IF readers' = 0 /\ ~QueueEmpty
           THEN awoken \cup { HeadReq.tid }
           ELSE awoken
       IN awoken' = newAwoken
    /\ UNCHANGED << lockW, lockU, lockB, queue >>

ReleaseWrite(t) ==
    /\ st[t] = "Writing"
    /\ st' = [st EXCEPT ![t] = "Idle"]
    /\ lockW' = 0
    /\ awoken' = awoken \cup AllWaitingTids(queue)
    /\ UNCHANGED << lockU, lockB, readers, queue >>

ReleaseUpread(t) ==
    /\ st[t] = "Upreading"
    /\ st' = [st EXCEPT ![t] = "Idle"]
    /\ lockU' = 0
    /\ awoken' = awoken \cup AllWaitingTids(queue)
    /\ UNCHANGED << lockW, lockB, readers, queue >>

\* Upgrade and downgrade operations
StartUpgrade(t) ==
    /\ st[t] = "Upreading"
    /\ lockB = 0
    /\ st' = [st EXCEPT ![t] = "Upgrading"]
    /\ lockB' = 1
    /\ UNCHANGED << lockW, lockU, readers, queue, awoken >>

UpgradeCommit(t) ==
    /\ st[t] = "Upgrading"
    /\ readers = 0
    /\ lockU = 1
    /\ lockB = 1
    /\ lockW = 0
    /\ st' = [st EXCEPT ![t] = "Writing"]
    /\ lockW' = 1
    /\ lockB' = 0
    /\ lockU' = 0
    /\ UNCHANGED << readers, queue, awoken >>

Downgrade(t) ==
    /\ st[t] = "Writing"
    /\ st' = [st EXCEPT ![t] = "Upreading"]
    /\ lockW' = 0
    /\ lockU' = 1
    /\ UNCHANGED << lockB, readers, queue, awoken >>

Next ==
    \E t \in THREADS:
        \/ CallReadAcquireNow(t)
        \/ CallReadEnqueue(t)
        \/ CallWriteAcquireNow(t)
        \/ CallWriteEnqueue(t)
        \/ CallUpreadAcquireNow(t)
        \/ CallUpreadEnqueue(t)
        \/ AcquireFromQueueRead(t)
        \/ AcquireFromQueueWrite(t)
        \/ AcquireFromQueueUpread(t)
        \/ ReleaseRead(t)
        \/ ReleaseWrite(t)
        \/ ReleaseUpread(t)
        \/ StartUpgrade(t)
        \/ UpgradeCommit(t)
        \/ Downgrade(t)

Spec ==
    Init /\ [][Next]_vars /\
    (\A t \in THREADS:
        WF_vars(AcquireFromQueueRead(t)) /\
        WF_vars(AcquireFromQueueWrite(t)) /\
        WF_vars(AcquireFromQueueUpread(t)) /\
        WF_vars(UpgradeCommit(t))
    )

====