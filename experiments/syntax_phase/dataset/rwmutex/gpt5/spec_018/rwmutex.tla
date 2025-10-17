---- MODULE rwmutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANT Proc

Ops == {"Read","Write","Upread"}
Holds == Ops \cup {"None"}

VARIABLES lock, queue, woken, hold, req, upgradingBy

TypeOK ==
    /\ lock \in [writer: BOOLEAN, upread: BOOLEAN, being: BOOLEAN, readers: Nat]
    /\ queue \in Seq([proc: Proc, op: Ops])
    /\ woken \subseteq Proc
    /\ hold \in [Proc -> Holds]
    /\ req \in [Proc -> (Ops \cup {"None"})]
    /\ upgradingBy \in (Proc \cup {"None"})

Init ==
    /\ lock = [writer |-> FALSE, upread |-> FALSE, being |-> FALSE, readers |-> 0]
    /\ queue = << >>
    /\ woken = {}
    /\ hold = [p \in Proc |-> "None"]
    /\ req = [p \in Proc |-> "None"]
    /\ upgradingBy = "None"

Tail(q) == IF Len(q) = 0 THEN << >> ELSE SubSeq(q, 2, Len(q))
QueueProcs(q) == { q[i].proc : i \in 1..Len(q) }
HeadProcSet(q) == IF Len(q) = 0 THEN {} ELSE { q[1].proc }
InQueue(p) == \E i \in 1..Len(queue): queue[i].proc = p

CanRead(l) == ~l.writer /\ ~l.being
CanWrite(l) == ~l.writer /\ ~l.upread /\ l.readers = 0
CanUpread(l) == ~l.writer /\ ~l.upread

Cond(l, op) ==
    IF op = "Read" THEN CanRead(l)
    ELSE IF op = "Write" THEN CanWrite(l)
    ELSE CanUpread(l)

LockAfterAcquire(l, op) ==
    IF op = "Read" THEN [l EXCEPT !.readers = @ + 1]
    ELSE IF op = "Write" THEN [l EXCEPT !.writer = TRUE]
    ELSE [l EXCEPT !.upread = TRUE]

Request(p, op) ==
    /\ p \in Proc
    /\ op \in Ops
    /\ req[p] = "None"
    /\ hold[p] = "None"
    /\ ~InQueue(p)
    /\ req' = [req EXCEPT ![p] = op]
    /\ UNCHANGED << lock, queue, woken, hold, upgradingBy >>

Enqueue(p) ==
    /\ p \in Proc
    /\ req[p] \in Ops
    /\ hold[p] = "None"
    /\ (Len(queue) # 0 \/ ~Cond(lock, req[p]))
    /\ ~InQueue(p)
    /\ queue' = Append(queue, [proc |-> p, op |-> req[p]])
    /\ req' = [req EXCEPT ![p] = "None"]
    /\ UNCHANGED << lock, woken, hold, upgradingBy >>

AcquireImm(p) ==
    /\ p \in Proc
    /\ req[p] \in Ops
    /\ hold[p] = "None"
    /\ Len(queue) = 0
    /\ Cond(lock, req[p])
    /\ lock' = LockAfterAcquire(lock, req[p])
    /\ hold' = [hold EXCEPT ![p] = req[p]]
    /\ req' = [req EXCEPT ![p] = "None"]
    /\ UNCHANGED << queue, woken, upgradingBy >>

AcquireFromQueue(p) ==
    /\ p \in Proc
    /\ Len(queue) \geq 1
    /\ queue[1].proc = p
    /\ p \in woken
    /\ hold[p] = "None"
    /\ Cond(lock, queue[1].op)
    /\ lock' = LockAfterAcquire(lock, queue[1].op)
    /\ hold' = [hold EXCEPT ![p] = queue[1].op]
    /\ queue' = Tail(queue)
    /\ woken' = woken \ {p}
    /\ UNCHANGED << req, upgradingBy >>

ReadReleaseWake(p) ==
    /\ p \in Proc
    /\ hold[p] = "Read"
    /\ lock.readers = 1
    /\ ~lock.writer /\ ~lock.upread /\ ~lock.being
    /\ lock' = [lock EXCEPT !.readers = 0]
    /\ hold' = [hold EXCEPT ![p] = "None"]
    /\ woken' = woken \cup HeadProcSet(queue)
    /\ UNCHANGED << queue, req, upgradingBy >>

ReadReleaseNoWake(p) ==
    /\ p \in Proc
    /\ hold[p] = "Read"
    /\ (lock.readers # 1 \/ lock.writer \/ lock.upread \/ lock.being)
    /\ lock.readers \geq 1
    /\ lock' = [lock EXCEPT !.readers = @ - 1]
    /\ hold' = [hold EXCEPT ![p] = "None"]
    /\ UNCHANGED << queue, woken, req, upgradingBy >>

WriteRelease(p) ==
    /\ p \in Proc
    /\ hold[p] = "Write"
    /\ lock.writer
    /\ lock' = [lock EXCEPT !.writer = FALSE]
    /\ hold' = [hold EXCEPT ![p] = "None"]
    /\ woken' = woken \cup QueueProcs(queue)
    /\ UNCHANGED << queue, req, upgradingBy >>

UpreadReleaseWake(p) ==
    /\ p \in Proc
    /\ hold[p] = "Upread"
    /\ lock.upread
    /\ ~lock.being
    /\ ~lock.writer
    /\ lock.readers = 0
    /\ lock' = [lock EXCEPT !.upread = FALSE]
    /\ hold' = [hold EXCEPT ![p] = "None"]
    /\ woken' = woken \cup QueueProcs(queue)
    /\ UNCHANGED << queue, req, upgradingBy >>

UpreadReleaseNoWake(p) ==
    /\ p \in Proc
    /\ hold[p] = "Upread"
    /\ lock.upread
    /\ ~lock.being
    /\ (lock.writer \/ lock.readers # 0)
    /\ lock' = [lock EXCEPT !.upread = FALSE]
    /\ hold' = [hold EXCEPT ![p] = "None"]
    /\ UNCHANGED << queue, woken, req, upgradingBy >>

Downgrade(p) ==
    /\ p \in Proc
    /\ hold[p] = "Write"
    /\ lock.writer
    /\ lock' = [lock EXCEPT !.writer = FALSE, !.upread = TRUE]
    /\ hold' = [hold EXCEPT ![p] = "Upread"]
    /\ UNCHANGED << queue, woken, req, upgradingBy >>

UpgradBegin(p) ==
    /\ p \in Proc
    /\ hold[p] = "Upread"
    /\ lock.upread
    /\ ~lock.being
    /\ lock' = [lock EXCEPT !.being = TRUE]
    /\ upgradingBy' = p
    /\ UNCHANGED << queue, woken, req, hold >>

TryUpgrade(p) ==
    /\ p \in Proc
    /\ hold[p] = "Upread"
    /\ upgradingBy = p
    /\ lock.upread
    /\ lock.being
    /\ ~lock.writer
    /\ lock.readers = 0
    /\ lock' = [lock EXCEPT !.being = FALSE, !.upread = FALSE, !.writer = TRUE]
    /\ hold' = [hold EXCEPT ![p] = "Write"]
    /\ upgradingBy' = "None"
    /\ UNCHANGED << queue, woken, req >>

Next ==
    \E p \in Proc, op \in Ops: Request(p, op)
    \/ \E p \in Proc: Enqueue(p)
    \/ \E p \in Proc: AcquireImm(p)
    \/ \E p \in Proc: AcquireFromQueue(p)
    \/ \E p \in Proc: ReadReleaseWake(p)
    \/ \E p \in Proc: ReadReleaseNoWake(p)
    \/ \E p \in Proc: WriteRelease(p)
    \/ \E p \in Proc: UpreadReleaseWake(p)
    \/ \E p \in Proc: UpreadReleaseNoWake(p)
    \/ \E p \in Proc: Downgrade(p)
    \/ \E p \in Proc: UpgradBegin(p)
    \/ \E p \in Proc: TryUpgrade(p)

AcquireFromQueueAny == \E p \in Proc: AcquireFromQueue(p)
ReadReleaseAny == \E p \in Proc: ReadReleaseWake(p) \/ ReadReleaseNoWake(p)
WriteReleaseAny == \E p \in Proc: WriteRelease(p)
UpreadReleaseAny == \E p \in Proc: UpreadReleaseWake(p) \/ UpreadReleaseNoWake(p)
TryUpgradeAny == \E p \in Proc: TryUpgrade(p)

Vars == << lock, queue, woken, hold, req, upgradingBy >>

Spec ==
    Init
    /\ [][Next]_Vars
    /\ WF_Vars(AcquireFromQueueAny)
    /\ WF_Vars(ReadReleaseAny)
    /\ WF_Vars(WriteReleaseAny)
    /\ WF_Vars(UpreadReleaseAny)
    /\ WF_Vars(TryUpgradeAny)
====