----------------------------- MODULE rwmutex -----------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* Constants --------------------------------------------------------------
\* Threads: finite set of worker identities to explore.
\* MaxReaders: upper bound corresponding to MAX_READER in the implementation.
CONSTANTS Threads, MaxReaders

\* A distinguished value used when no thread occupies a role.
NoThread == "NoThread"

\* Operation tags covering the three public lock calls plus upgrade spin.
Ops == {"Read", "Write", "Upread", "Upgrade"}

\* Thread lifecycle buckets we will refine in the state machine.
ThreadPhases ==
    {"Idle", "ReadHolding", "ReadWaiting",
     "WriteHolding", "WriteWaiting",
     "UpreadHolding", "UpreadWaiting",
     "UpgradeSpinning", "DowngradeInFlight"}

\* Derived domain helpers.
ThreadRoleDomain == Threads \cup {NoThread}
ReaderCountDomain == 0 .. MaxReaders

\* Typing helpers for structured state components.
LockRecord ==
    [ writerOwner: ThreadRoleDomain,
      upgradableOwner: ThreadRoleDomain,
      upgradingOwner: ThreadRoleDomain,
      readerCount: ReaderCountDomain ]

WaitEntry ==
    [ tid: Threads,
      op: Ops ]

ThreadStateRecord ==
    [ phase: ThreadPhases,
      readHolds: Nat,
      queuedOp: Ops \cup {"None"} ]

WaitQueueState == Seq(WaitEntry)

\* Variables --------------------------------------------------------------
\* lock: snapshot of the atomic bitfield decoded into explicit roles.
\* waitQueue: abstract FIFO capturing the single WaitQueue in the code.
\* threadState: per-thread bookkeeping for acquisitions and pending ops.
\* pendingWakeUps: set of threads that have been woken but not yet retried.
\* expectedWakeUps: ghost set tracking threads that must observe a wake event.
\* enqueueEpoch: ghost counter recording each thread's enqueue round.
\* wakeEpoch: ghost counter recording successful wakes per thread.
VARIABLES lock, waitQueue, threadState, pendingWakeUps, expectedWakeUps, enqueueEpoch, wakeEpoch

\* ------------------------------------------------------------------------
\* Helper predicates and initialisation

ThreadStateInit ==
    [t \in Threads |->
        [ phase |-> "Idle",
          readHolds |-> 0,
          queuedOp |-> "None"]]

LockInit ==
    [ writerOwner |-> NoThread,
      upgradableOwner |-> NoThread,
      upgradingOwner |-> NoThread,
      readerCount |-> 0 ]

Init ==
    /\ lock = LockInit
    /\ waitQueue = << >>
    /\ threadState = ThreadStateInit
    /\ pendingWakeUps = {}
    /\ expectedWakeUps = {}
    /\ enqueueEpoch = [t \in Threads |-> 0]
    /\ wakeEpoch = [t \in Threads |-> 0]

ThreadStateOK(ts) ==
    /\ DOMAIN ts = Threads
    /\ \A t \in Threads :
        LET st == ts[t] IN
            /\ st \in ThreadStateRecord
            /\ st.readHolds = 0
                  \/ st.phase \in {"ReadHolding", "DowngradeInFlight"}
            /\ st.phase = "ReadHolding" => st.readHolds \in Nat \ {0}
            /\ st.phase # "ReadHolding" => st.readHolds = 0

LockStateOK(lk) ==
    /\ lk \in LockRecord
    /\ lk.readerCount \in 0 .. MaxReaders
    /\ (lk.writerOwner = NoThread) \/ (lk.writerOwner \in Threads)
    /\ (lk.upgradableOwner = NoThread) \/ (lk.upgradableOwner \in Threads)
    /\ (lk.upgradingOwner = NoThread) \/ (lk.upgradingOwner \in Threads)
    /\ lk.writerOwner /= NoThread
          => lk.readerCount = 0 /\ lk.upgradableOwner = NoThread
    /\ lk.upgradingOwner # NoThread => lk.upgradableOwner # NoThread

QueueOK(q) ==
    /\ q \in WaitQueueState
    /\ \A i \in DOMAIN q :
        LET e == q[i] IN
            /\ e.tid \in Threads
            /\ e.op \in Ops

PendingWakeUpsOK(pw) ==
    /\ pw \subseteq Threads

ExpectedWakeUpsOK(ew) ==
    ew \subseteq Threads

EpochsOK(enq, wk) ==
    /\ DOMAIN enq = Threads
    /\ DOMAIN wk = Threads
    /\ \A t \in Threads :
        /\ enq[t] \in Nat
        /\ wk[t] \in Nat
        /\ wk[t] <= enq[t]

TypeInvariant ==
    /\ LockStateOK(lock)
    /\ ThreadStateOK(threadState)
    /\ QueueOK(waitQueue)
    /\ PendingWakeUpsOK(pendingWakeUps)
    /\ ExpectedWakeUpsOK(expectedWakeUps)
    /\ EpochsOK(enqueueEpoch, wakeEpoch)

Min(S) ==
    CHOOSE m \in S : \A n \in S : m <= n

\* helper update macros

UpdateThreadState(ts, t, new) ==
    [ts EXCEPT ![t] = new]

AppendEntry(q, entry) == Append(q, entry)

DropIndex(q, idx) ==
    IF idx = 0 THEN q
    ELSE
        LET front == SubSeq(q, 1, idx - 1) IN
        LET back == SubSeq(q, idx + 1, Len(q)) IN
            front \o back

SeqToSet(s) == { s[i] : i \in 1 .. Len(s) }

FirstMatchIndex(q, cond(_)) ==
    LET idxs == {i \in 1 .. Len(q) : cond(q[i])} IN
        IF idxs = {} THEN 0 ELSE Min(idxs)

RemoveFirstMatch(q, cond(_)) ==
    LET idx == FirstMatchIndex(q, cond) IN
        IF idx = 0
            THEN [queue |-> q, found |-> FALSE, entry |-> [tid |-> NoThread, op |-> "Read"]]
            ELSE [queue |-> DropIndex(q, idx),
                   found |-> TRUE,
                   entry |-> q[idx]]

ThreadIsQueuedFor(ts, t, op) ==
    \E i \in 1 .. Len(waitQueue) :
        /\ waitQueue[i].tid = t
        /\ waitQueue[i].op = op

EnqueueEpochInc(epoch, t) ==
    [epoch EXCEPT ![t] = epoch[t] + 1]

WakeEpochUpdate(epoch, S) ==
    [tid \in Threads |->
        IF tid \in S THEN enqueueEpoch[tid] ELSE epoch[tid]]

ClearQueuedOp(ts, tid) ==
    UpdateThreadState(ts, tid, [ts[tid] EXCEPT !.queuedOp = "None"])

ClearQueuedOps(ts, tids) ==
    [t \in Threads |->
        IF t \in tids
            THEN [ts[t] EXCEPT !.queuedOp = "None"]
            ELSE ts[t]]

PopFront(q) ==
    IF Len(q) = 0
        THEN [queue |-> q, found |-> FALSE, entry |-> [tid |-> NoThread, op |-> "Read"]]
        ELSE [queue |-> Tail(q),
              found |-> TRUE,
              entry |-> Head(q)]

PhaseWaiting(op) ==
    CASE op = "Read" -> "ReadWaiting"
       [] op = "Write" -> "WriteWaiting"
       [] op = "Upread" -> "UpreadWaiting"
       [] op = "Upgrade" -> "UpgradeSpinning"
       [] OTHER -> "Idle"

PhaseHolding(op) ==
    CASE op = "Read" -> "ReadHolding"
       [] op = "Write" -> "WriteHolding"
       [] op = "Upread" -> "UpreadHolding"
       [] op = "Upgrade" -> "WriteHolding"
       [] OTHER -> "Idle"

AddReader(lk) ==
    [lk EXCEPT !.readerCount = lk.readerCount + 1]

RemoveReader(lk) ==
    [lk EXCEPT !.readerCount = lk.readerCount - 1]

SetWriter(lk, t) ==
    [lk EXCEPT !.writerOwner = t]

ClearWriter(lk) ==
    [lk EXCEPT !.writerOwner = NoThread]

SetUpgrader(lk, t) ==
    [lk EXCEPT !.upgradingOwner = t]

ClearUpgrader(lk) ==
    [lk EXCEPT !.upgradingOwner = NoThread]

SetUpgradeable(lk, t) ==
    [lk EXCEPT !.upgradableOwner = t]

ClearUpgradeable(lk) ==
    [lk EXCEPT !.upgradableOwner = NoThread]

WaitingPredicate(e) ==
    /\ threadState[e.tid].phase = PhaseWaiting(e.op)
    /\ threadState[e.tid].queuedOp = e.op

QueuedThreadSet(q) == { q[i].tid : i \in 1 .. Len(q) }

WakeTargets(q) ==
    LET waitingIdxs == { i \in 1 .. Len(q) : WaitingPredicate(q[i]) } IN
        { q[i].tid : i \in waitingIdxs }

FirstTargets(entry, found) ==
    IF found /\ WaitingPredicate(entry)
        THEN {entry.tid}
        ELSE {}

WakeAllThreadState(ts, q) ==
    LET tids == WakeTargets(q) IN ClearQueuedOps(ts, tids)

WakeOneThreadState(ts, entry, found) ==
    IF found THEN ClearQueuedOp(ts, entry.tid) ELSE ts

\* Action definitions -----------------------------------------------------

RequestRead(t) ==
    LET st == threadState[t] IN
    /\ t \in Threads
    /\ st.phase = "Idle"
    /\ threadState' =
        UpdateThreadState(threadState, t,
            [st EXCEPT !.phase = "ReadWaiting",
                       !.queuedOp = "None"])
    /\ UNCHANGED << lock, waitQueue, pendingWakeUps, expectedWakeUps, enqueueEpoch, wakeEpoch >>

RequestWrite(t) ==
    LET st == threadState[t] IN
    /\ t \in Threads
    /\ st.phase = "Idle"
    /\ threadState' =
        UpdateThreadState(threadState, t,
            [st EXCEPT !.phase = "WriteWaiting",
                       !.queuedOp = "None"])
    /\ UNCHANGED << lock, waitQueue, pendingWakeUps, expectedWakeUps, enqueueEpoch, wakeEpoch >>

RequestUpread(t) ==
    LET st == threadState[t] IN
    /\ t \in Threads
    /\ st.phase = "Idle"
    /\ threadState' =
        UpdateThreadState(threadState, t,
            [st EXCEPT !.phase = "UpreadWaiting",
                       !.queuedOp = "None"])
    /\ UNCHANGED << lock, waitQueue, pendingWakeUps, expectedWakeUps, enqueueEpoch, wakeEpoch >>

TryReadAcquireSuccess(t) ==
    LET st == threadState[t] IN
    /\ t \in Threads
    /\ st.phase = "ReadWaiting"
    /\ st.queuedOp = "None"
    /\ lock.writerOwner = NoThread
    /\ lock.upgradingOwner = NoThread
    /\ lock.readerCount < MaxReaders
    /\ lock' = AddReader(lock)
    /\ threadState' =
        UpdateThreadState(threadState, t,
            [st EXCEPT !.phase = "ReadHolding",
                       !.readHolds = st.readHolds + 1])
    /\ pendingWakeUps' = pendingWakeUps \ {t}
    /\ expectedWakeUps' = expectedWakeUps \ {t}
    /\ waitQueue' = waitQueue
    /\ enqueueEpoch' = enqueueEpoch
    /\ wakeEpoch' = wakeEpoch

TryReadAcquireFail(t) ==
    LET st == threadState[t] IN
    /\ t \in Threads
    /\ st.phase = "ReadWaiting"
    /\ st.queuedOp = "None"
    /\ lock.readerCount = MaxReaders
        \/ lock.writerOwner # NoThread
        \/ lock.upgradingOwner # NoThread
    /\ lock' = lock
    /\ threadState' =
        UpdateThreadState(threadState, t,
            [st EXCEPT !.queuedOp = "Read"])
    /\ waitQueue' =
        AppendEntry(waitQueue,
            [tid |-> t, op |-> "Read"])
    /\ pendingWakeUps' = pendingWakeUps \ {t}
    /\ expectedWakeUps' = expectedWakeUps \ {t}
    /\ enqueueEpoch' = EnqueueEpochInc(enqueueEpoch, t)
    /\ wakeEpoch' = wakeEpoch

ReadReleaseNonLast(t) ==
    LET st == threadState[t] IN
    /\ t \in Threads
    /\ st.phase = "ReadHolding"
    /\ st.readHolds > 0
    /\ lock.readerCount > 1
    /\ lock' = RemoveReader(lock)
    /\ threadState' =
        UpdateThreadState(threadState, t,
            [st EXCEPT !.readHolds = st.readHolds - 1,
                       !.phase =
                        IF st.readHolds = 1 THEN "Idle" ELSE "ReadHolding"])
    /\ UNCHANGED << waitQueue, pendingWakeUps, expectedWakeUps, enqueueEpoch, wakeEpoch >>

ReadReleaseLast(t) ==
    LET st == threadState[t] IN
    LET res ==
        RemoveFirstMatch(waitQueue,
            LAMBDA e: WaitingPredicate(e)) IN
    /\ t \in Threads
    /\ st.phase = "ReadHolding"
    /\ st.readHolds > 0
    /\ lock.readerCount = 1
    /\ lock' = RemoveReader(lock)
    /\ LET wset == IF res.found THEN {res.entry.tid} ELSE {} IN
        /\ waitQueue' = res.queue
        /\ pendingWakeUps' =
            IF res.found THEN pendingWakeUps \cup wset
                        ELSE pendingWakeUps
        /\ expectedWakeUps' =
            IF res.found THEN expectedWakeUps \cup wset ELSE expectedWakeUps
        /\ enqueueEpoch' = enqueueEpoch
        /\ wakeEpoch' = WakeEpochUpdate(wakeEpoch, wset)
        /\ threadState' =
            IF res.found
                THEN UpdateThreadState(
                        UpdateThreadState(threadState, t,
                            [st EXCEPT !.readHolds = st.readHolds - 1,
                                    !.phase =
                                        IF st.readHolds = 1 THEN "Idle" ELSE "ReadHolding"]),
                        res.entry.tid,
                        [threadState[res.entry.tid] EXCEPT !.queuedOp = "None"])
                ELSE UpdateThreadState(threadState, t,
                        [st EXCEPT !.readHolds = st.readHolds - 1,
                                !.phase =
                                        IF st.readHolds = 1 THEN "Idle" ELSE "ReadHolding"])

TryWriteAcquireSuccess(t) ==
    LET st == threadState[t] IN
    /\ t \in Threads
    /\ st.phase = "WriteWaiting"
    /\ st.queuedOp = "None"
    /\ lock.readerCount = 0
    /\ lock.writerOwner = NoThread
    /\ lock.upgradableOwner = NoThread
    /\ lock.upgradingOwner = NoThread
    /\ lock' = SetWriter(lock, t)
    /\ threadState' =
        UpdateThreadState(threadState, t,
            [st EXCEPT !.phase = "WriteHolding"])
    /\ pendingWakeUps' = pendingWakeUps \ {t}
    /\ expectedWakeUps' = expectedWakeUps \ {t}
    /\ waitQueue' = waitQueue
    /\ enqueueEpoch' = enqueueEpoch
    /\ wakeEpoch' = wakeEpoch

TryWriteAcquireFail(t) ==
    LET st == threadState[t] IN
    /\ t \in Threads
    /\ st.phase = "WriteWaiting"
    /\ st.queuedOp = "None"
    /\ lock.readerCount # 0
        \/ lock.writerOwner # NoThread
        \/ lock.upgradableOwner # NoThread
        \/ lock.upgradingOwner # NoThread
    /\ lock' = lock
    /\ threadState' =
        UpdateThreadState(threadState, t,
            [st EXCEPT !.queuedOp = "Write"])
    /\ waitQueue' =
        AppendEntry(waitQueue,
            [tid |-> t, op |-> "Write"])
    /\ pendingWakeUps' = pendingWakeUps \ {t}
    /\ expectedWakeUps' = expectedWakeUps \ {t}
    /\ enqueueEpoch' = EnqueueEpochInc(enqueueEpoch, t)
    /\ wakeEpoch' = wakeEpoch

WriteRelease(t) ==
    LET st == threadState[t] IN
    LET targets == WakeTargets(waitQueue) IN
    /\ t \in Threads
    /\ st.phase = "WriteHolding"
    /\ lock.writerOwner = t
    /\ lock.readerCount = 0
    /\ lock' = ClearWriter(lock)
    /\ waitQueue' = << >>
    /\ pendingWakeUps' = pendingWakeUps \cup targets
    /\ expectedWakeUps' = expectedWakeUps \cup targets
    /\ enqueueEpoch' = enqueueEpoch
    /\ wakeEpoch' = WakeEpochUpdate(wakeEpoch, targets)
    /\ threadState' =
        ClearQueuedOps(
            UpdateThreadState(threadState, t,
                [st EXCEPT !.phase = "Idle"]),
            targets)

TryUpreadAcquireSuccess(t) ==
    LET st == threadState[t] IN
    /\ t \in Threads
    /\ st.phase = "UpreadWaiting"
    /\ st.queuedOp = "None"
    /\ lock.writerOwner = NoThread
    /\ lock.upgradableOwner = NoThread
    /\ lock' = SetUpgradeable(lock, t)
    /\ threadState' =
        UpdateThreadState(threadState, t,
            [st EXCEPT !.phase = "UpreadHolding"])
    /\ pendingWakeUps' = pendingWakeUps \ {t}
    /\ expectedWakeUps' = expectedWakeUps \ {t}
    /\ waitQueue' = waitQueue
    /\ enqueueEpoch' = enqueueEpoch
    /\ wakeEpoch' = wakeEpoch

TryUpreadAcquireFail(t) ==
    LET st == threadState[t] IN
    /\ t \in Threads
    /\ st.phase = "UpreadWaiting"
    /\ st.queuedOp = "None"
    /\ lock.writerOwner # NoThread
        \/ lock.upgradableOwner # NoThread
    /\ lock' = lock
    /\ threadState' =
        UpdateThreadState(threadState, t,
            [st EXCEPT !.queuedOp = "Upread"])
    /\ waitQueue' =
        AppendEntry(waitQueue,
            [tid |-> t, op |-> "Upread"])
    /\ pendingWakeUps' = pendingWakeUps \ {t}
    /\ expectedWakeUps' = expectedWakeUps \ {t}
    /\ enqueueEpoch' = EnqueueEpochInc(enqueueEpoch, t)
    /\ wakeEpoch' = wakeEpoch


    \* LET awakenAll
    \*     lock.readerCount = 0
    \*         /\ lock.writerOwner = NoThread
    \*         /\ lock.upgradingOwner = NoThread IN

UpreadRelease(t) ==
    LET st == threadState[t] IN
    LET awakenAll == 
        lock.readerCount = 0
            /\ lock.writerOwner = NoThread
            /\ lock.upgradingOwner = NoThread IN
    LET targets == IF awakenAll THEN WakeTargets(waitQueue) ELSE {} IN
    /\ t \in Threads
    /\ st.phase = "UpreadHolding"
    /\ lock.upgradableOwner = t
    /\ lock' = ClearUpgradeable(lock)
    /\ waitQueue' = IF awakenAll THEN << >> ELSE waitQueue
    /\ pendingWakeUps' =
        IF awakenAll THEN pendingWakeUps \cup targets ELSE pendingWakeUps
    /\ expectedWakeUps' =
        IF awakenAll THEN expectedWakeUps \cup targets ELSE expectedWakeUps
    /\ enqueueEpoch' = enqueueEpoch
    /\ wakeEpoch' =
        IF awakenAll THEN WakeEpochUpdate(wakeEpoch, targets) ELSE wakeEpoch
    /\ threadState' =
        IF awakenAll
            THEN ClearQueuedOps(
                    UpdateThreadState(threadState, t,
                        [st EXCEPT !.phase = "Idle"]),
                    targets)
            ELSE UpdateThreadState(threadState, t,
                    [st EXCEPT !.phase = "Idle"])

UpgradeStart(t) ==
    LET st == threadState[t] IN
    /\ t \in Threads
    /\ st.phase = "UpreadHolding"
    /\ lock.upgradableOwner = t
    /\ lock.upgradingOwner = NoThread
    /\ lock' = SetUpgrader(lock, t)
    /\ threadState' =
        UpdateThreadState(threadState, t,
            [st EXCEPT !.phase = "UpgradeSpinning"])
    /\ UNCHANGED << waitQueue, pendingWakeUps, expectedWakeUps, enqueueEpoch, wakeEpoch >>

UpgradeCommit(t) ==
    LET st == threadState[t] IN
    /\ t \in Threads
    /\ st.phase = "UpgradeSpinning"
    /\ lock.upgradableOwner = t
    /\ lock.upgradingOwner = t
    /\ lock.readerCount = 0
    /\ lock.writerOwner = NoThread
    /\ lock' =
        ClearUpgradeable(
            ClearUpgrader(
                SetWriter(lock, t)))
    /\ threadState' =
        UpdateThreadState(threadState, t,
            [st EXCEPT !.phase = "WriteHolding"])
    /\ pendingWakeUps' = pendingWakeUps
    /\ expectedWakeUps' = expectedWakeUps
    /\ waitQueue' = waitQueue
    /\ enqueueEpoch' = enqueueEpoch
    /\ wakeEpoch' = wakeEpoch

UpgradeSpinStutter(t) ==
    LET st == threadState[t] IN
    /\ t \in Threads
    /\ st.phase = "UpgradeSpinning"
    /\ (lock.readerCount # 0 \/ lock.writerOwner # NoThread)
    /\ UNCHANGED << lock, waitQueue, threadState, pendingWakeUps, expectedWakeUps, enqueueEpoch, wakeEpoch >>

DowngradeCommit(t) ==
    LET st == threadState[t] IN
    LET targets == WakeTargets(waitQueue) IN
    /\ t \in Threads
    /\ st.phase = "WriteHolding"
    /\ lock.writerOwner = t
    /\ lock.readerCount = 0
    /\ lock' =
        SetUpgradeable(
            ClearWriter(lock), t)
    /\ waitQueue' = << >>
    /\ pendingWakeUps' = pendingWakeUps \cup targets
    /\ expectedWakeUps' = expectedWakeUps \cup targets
    /\ enqueueEpoch' = enqueueEpoch
    /\ wakeEpoch' = WakeEpochUpdate(wakeEpoch, targets)
    /\ threadState' =
        ClearQueuedOps(
            UpdateThreadState(threadState, t,
                [st EXCEPT !.phase = "UpreadHolding"]),
            targets)

DeliverWake(t) ==
    LET st == threadState[t] IN
    /\ t \in Threads
    /\ t \in pendingWakeUps
    /\ threadState' =
        UpdateThreadState(threadState, t,
            [st EXCEPT !.queuedOp = "None"])
    /\ pendingWakeUps' = pendingWakeUps \ {t}
    /\ expectedWakeUps' = expectedWakeUps \ {t}
    /\ UNCHANGED << lock, waitQueue, enqueueEpoch, wakeEpoch >>


vars == <<lock, waitQueue, threadState, pendingWakeUps, expectedWakeUps, enqueueEpoch, wakeEpoch>>

Next ==
    \E t \in Threads :
        RequestRead(t)
        \/ RequestWrite(t)
        \/ RequestUpread(t)
        \/ TryReadAcquireSuccess(t)
        \/ TryReadAcquireFail(t)
        \/ ReadReleaseNonLast(t)
        \/ ReadReleaseLast(t)
        \/ TryWriteAcquireSuccess(t)
        \/ TryWriteAcquireFail(t)
        \/ WriteRelease(t)
        \/ TryUpreadAcquireSuccess(t)
        \/ TryUpreadAcquireFail(t)
        \/ UpreadRelease(t)
        \/ UpgradeStart(t)
        \/ UpgradeCommit(t)
        \/ UpgradeSpinStutter(t)
        \/ DowngradeCommit(t)
    \/ DeliverWake(t)

Progress(t) ==
    TryReadAcquireSuccess(t)
    \/ TryWriteAcquireSuccess(t)
    \/ TryUpreadAcquireSuccess(t)
    \/ UpgradeCommit(t)
    \/ DowngradeCommit(t)
    \/ DeliverWake(t)

Fairness ==
    \A t \in Threads : WF_vars(Progress(t))

Spec ==
    Init /\ [][Next]_vars /\ Fairness

MutualExclusion ==
    /\ (lock.writerOwner = NoThread \/ lock.readerCount = 0)
    /\ (lock.writerOwner = NoThread \/ lock.upgradableOwner = NoThread)

RECURSIVE SumThreadReadHolds(_,_)

SumThreadReadHolds(S, ts) ==
    IF S = {}
        THEN 0
        ELSE
            LET t == CHOOSE x \in S : TRUE IN
                ts[t].readHolds + SumThreadReadHolds(S \ {t}, ts)

SumReadHolds(ts) ==
    SumThreadReadHolds(Threads, ts)

ReaderAccounting ==
    lock.readerCount = SumReadHolds(threadState)

OwnershipConsistency ==
    /\ (lock.writerOwner = NoThread
        => \A t \in Threads : threadState[t].phase # "WriteHolding")
    /\ (lock.writerOwner # NoThread
        => /\ threadState[lock.writerOwner].phase = "WriteHolding"
           /\ \A t \in Threads \ {lock.writerOwner} :
                threadState[t].phase # "WriteHolding")
    /\ \A t \in Threads :
        threadState[t].phase = "WriteHolding" => lock.writerOwner = t
    /\ (lock.upgradableOwner # NoThread
        => /\ threadState[lock.upgradableOwner].phase \in {"UpreadHolding", "UpgradeSpinning"}
           /\ \A t \in Threads \ {lock.upgradableOwner} :
                threadState[t].phase # "UpreadHolding" /\ threadState[t].phase # "UpgradeSpinning")
    /\ \A t \in Threads :
        threadState[t].phase = "UpreadHolding" => lock.upgradableOwner = t
    /\ \A t \in Threads :
        threadState[t].phase = "UpgradeSpinning" =>
            /\ lock.upgradableOwner = t
            /\ lock.upgradingOwner = t
    /\ (lock.upgradingOwner # NoThread
        => /\ lock.upgradableOwner = lock.upgradingOwner
           /\ threadState[lock.upgradingOwner].phase = "UpgradeSpinning")

QueueConsistency ==
    /\ \A i \in 1 .. Len(waitQueue) :
        LET e == waitQueue[i] IN
            /\ WaitingPredicate(e)
            /\ e.tid \notin pendingWakeUps
    /\ \A t \in Threads :
        Cardinality({ i \in 1 .. Len(waitQueue) : waitQueue[i].tid = t }) <= 1

PendingWakeConsistency ==
    /\ pendingWakeUps \cap QueuedThreadSet(waitQueue) = {}
    /\ \A t \in pendingWakeUps :
        /\ threadState[t].phase \in {"ReadWaiting", "WriteWaiting", "UpreadWaiting"}
        /\ threadState[t].queuedOp = "None"

QueuedOpConsistency ==
    \A t \in Threads :
        threadState[t].queuedOp \in Ops =>
            t \in QueuedThreadSet(waitQueue)

PendingReturnConsistency ==
    \A t \in Threads :
        t \in pendingWakeUps =>
            /\ threadState[t].queuedOp = "None"
            /\ threadState[t].phase \in {"ReadWaiting", "WriteWaiting", "UpreadWaiting"}

RequeueOrProgress ==
    \A t \in Threads :
        threadState[t].phase \in {"ReadWaiting", "WriteWaiting", "UpreadWaiting"} =>
            (t \in pendingWakeUps
             \/ t \in QueuedThreadSet(waitQueue)
             \/ threadState[t].queuedOp = "None")

ExpectedWakeSubset ==
    expectedWakeUps \subseteq pendingWakeUps

QueueEpochRelation ==
    \A t \in Threads :
        IF t \in QueuedThreadSet(waitQueue)
            THEN enqueueEpoch[t] = wakeEpoch[t] + 1
            ELSE enqueueEpoch[t] = wakeEpoch[t]

WaitQueueProgress ==
    Len(waitQueue) = 0
    \/ lock.readerCount > 0
    \/ lock.writerOwner # NoThread
    \/ lock.upgradableOwner # NoThread
    \/ lock.upgradingOwner # NoThread
    \/ pendingWakeUps # {}
    \/ \E t \in Threads :
        /\ threadState[t].phase \in {"ReadWaiting", "WriteWaiting", "UpreadWaiting"}
        /\ threadState[t].queuedOp = "None"

RWMInvariant ==
    TypeInvariant
    /\ MutualExclusion
    /\ ReaderAccounting
    /\ OwnershipConsistency
    /\ QueueConsistency
    /\ PendingWakeConsistency
    /\ QueuedOpConsistency
    /\ PendingReturnConsistency
    /\ RequeueOrProgress
    /\ ExpectedWakeSubset
    /\ QueueEpochRelation
    /\ WaitQueueProgress

ReadersOnlyConstraint ==
    /\ lock.writerOwner = NoThread
    /\ lock.upgradableOwner = NoThread
    /\ lock.upgradingOwner = NoThread
    /\ \A t \in Threads :
        /\ threadState[t].phase \in {"Idle", "ReadWaiting", "ReadHolding"}
        /\ threadState[t].queuedOp \in {"None", "Read"}
    /\ \A e \in SeqToSet(waitQueue) : e.op = "Read"

UpreadOnlyConstraint ==
    /\ lock.readerCount = 0
    /\ \A t \in Threads :
        /\ threadState[t].phase \in {"Idle", "UpreadWaiting", "UpreadHolding", "UpgradeSpinning", "WriteHolding"}
        /\ threadState[t].queuedOp \in {"None", "Upread"}
    /\ \A e \in SeqToSet(waitQueue) : e.op = "Upread"

DowngradeUpgradeConstraint ==
    /\ \A t \in Threads :
        /\ threadState[t].phase \in {"Idle", "WriteWaiting", "WriteHolding", "UpreadHolding", "UpgradeSpinning"}
        /\ threadState[t].queuedOp \in {"None", "Write"}
    /\ \A e \in SeqToSet(waitQueue) : e.op = "Write"

EventuallyIdle ==
    <> (lock.writerOwner = NoThread /\ lock.upgradableOwner = NoThread /\ lock.upgradingOwner = NoThread /\ lock.readerCount = 0)

=============================================================================
