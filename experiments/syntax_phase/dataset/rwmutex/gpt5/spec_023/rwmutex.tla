---- MODULE raftkvs ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS
    Threads,
    R, U, W,
    None

VARIABLES
    Q,
    Awakened,
    Readers,
    Writer,
    Upgrader,
    BeingUpgraded

vars == << Q, Awakened, Readers, Writer, Upgrader, BeingUpgraded >>

InQ(t) ==
    \E i \in 1..Len(Q): Q[i].tid = t

TidsOf(s) ==
    { s[i].tid : i \in 1..Len(s) }

HeadAwaken(s) ==
    IF Len(s) = 0 THEN {} ELSE { s[1].tid }

RemoveAtLocal(s, i) ==
    SubSeq(s, 1, i-1) \o SubSeq(s, i+1, Len(s))

RemoveFirstLocal(s, t, k) ==
    LET I == { i \in 1..Len(s): s[i].tid = t /\ s[i].kind = k }
    IN RemoveAtLocal(s, CHOOSE i \in I: TRUE)

ReaderPrefixIdxs(s) ==
    LET n ==
        IF Len(s) = 0 THEN 0
        ELSE CHOOSE k \in 0..Len(s):
            /\ \A i \in 1..k: s[i].kind = R
            /\ (k = Len(s) \/ s[k+1].kind # R)
    IN 1..n

AllowRead ==
    /\ Writer = None
    /\ BeingUpgraded = FALSE

LockIdle ==
    /\ Writer = None
    /\ Upgrader = None
    /\ Readers = {}
    /\ BeingUpgraded = FALSE

NotHolding(t) ==
    /\ ~(t \in Readers)
    /\ Writer # t
    /\ Upgrader # t

Init ==
    /\ Q = << >>
    /\ Awakened = {}
    /\ Readers = {}
    /\ Writer = None
    /\ Upgrader = None
    /\ BeingUpgraded = FALSE

ReadRequest(t) ==
    /\ t \in Threads
    /\ NotHolding(t)
    /\ ~InQ(t)
    /\ Q' = Q \o << [tid |-> t, kind |-> R] >>
    /\ UNCHANGED << Awakened, Readers, Writer, Upgrader, BeingUpgraded >>

WriteRequest(t) ==
    /\ t \in Threads
    /\ NotHolding(t)
    /\ ~InQ(t)
    /\ Q' = Q \o << [tid |-> t, kind |-> W] >>
    /\ UNCHANGED << Awakened, Readers, Writer, Upgrader, BeingUpgraded >>

UpreadRequest(t) ==
    /\ t \in Threads
    /\ NotHolding(t)
    /\ ~InQ(t)
    /\ Q' = Q \o << [tid |-> t, kind |-> U] >>
    /\ UNCHANGED << Awakened, Readers, Writer, Upgrader, BeingUpgraded >>

ReadAcquire(t) ==
    /\ t \in Threads
    /\ \E i \in ReaderPrefixIdxs(Q): Q[i].tid = t /\ Q[i].kind = R
    /\ AllowRead
    /\ NotHolding(t)
    /\ (t \in Awakened \/ LockIdle)
    /\ Q' = RemoveFirstLocal(Q, t, R)
    /\ Readers' = Readers \cup {t}
    /\ UNCHANGED << Awakened, Writer, Upgrader, BeingUpgraded >>

WriteAcquire(t) ==
    /\ t \in Threads
    /\ Len(Q) >= 1
    /\ Q[1].tid = t /\ Q[1].kind = W
    /\ Writer = None
    /\ Upgrader = None
    /\ Readers = {}
    /\ BeingUpgraded = FALSE
    /\ (t \in Awakened \/ LockIdle)
    /\ Q' = SubSeq(Q, 2, Len(Q))
    /\ Writer' = t
    /\ UNCHANGED << Awakened, Readers, Upgrader, BeingUpgraded >>

UpreadAcquire(t) ==
    /\ t \in Threads
    /\ Len(Q) >= 1
    /\ Q[1].tid = t /\ Q[1].kind = U
    /\ Writer = None
    /\ Upgrader = None
    /\ (t \in Awakened \/ LockIdle)
    /\ Q' = SubSeq(Q, 2, Len(Q))
    /\ Upgrader' = t
    /\ UNCHANGED << Awakened, Readers, Writer, BeingUpgraded >>

ReadRelease(t) ==
    /\ t \in Threads
    /\ t \in Readers
    /\ Q' = Q
    /\ Readers' = Readers \ { t }
    /\ Writer' = Writer
    /\ Upgrader' = Upgrader
    /\ BeingUpgraded' = BeingUpgraded
    /\ Awakened' =
        IF Readers' = {} /\ Writer = None /\ Upgrader = None /\ BeingUpgraded = FALSE
        THEN HeadAwaken(Q)
        ELSE Awakened

WriteRelease(t) ==
    /\ t \in Threads
    /\ Writer = t
    /\ Q' = Q
    /\ Writer' = None
    /\ Upgrader' = Upgrader
    /\ Readers' = Readers
    /\ BeingUpgraded' = BeingUpgraded
    /\ Awakened' = TidsOf(Q)

UpreadRelease(t) ==
    /\ t \in Threads
    /\ Upgrader = t
    /\ BeingUpgraded = FALSE
    /\ Q' = Q
    /\ Upgrader' = None
    /\ Writer' = Writer
    /\ Readers' = Readers
    /\ BeingUpgraded' = BeingUpgraded
    /\ Awakened' =
        IF Readers = {} /\ Writer = None /\ BeingUpgraded = FALSE
        THEN TidsOf(Q)
        ELSE Awakened

UpgradeBegin(t) ==
    /\ t \in Threads
    /\ Upgrader = t
    /\ Writer = None
    /\ BeingUpgraded = FALSE
    /\ BeingUpgraded' = TRUE
    /\ UNCHANGED << Q, Awakened, Readers, Writer, Upgrader >>

UpgradeCommit(t) ==
    /\ t \in Threads
    /\ Upgrader = t
    /\ Writer = None
    /\ BeingUpgraded = TRUE
    /\ Readers = {}
    /\ Writer' = t
    /\ Upgrader' = None
    /\ BeingUpgraded' = FALSE
    /\ UNCHANGED << Q, Awakened, Readers >>

Downgrade(t) ==
    /\ t \in Threads
    /\ Writer = t
    /\ Upgrader' = t
    /\ Writer' = None
    /\ UNCHANGED << Q, Awakened, Readers, BeingUpgraded >>

Next ==
    \/ \E t \in Threads: ReadRequest(t)
    \/ \E t \in Threads: WriteRequest(t)
    \/ \E t \in Threads: UpreadRequest(t)
    \/ \E t \in Threads: ReadAcquire(t)
    \/ \E t \in Threads: WriteAcquire(t)
    \/ \E t \in Threads: UpreadAcquire(t)
    \/ \E t \in Threads: ReadRelease(t)
    \/ \E t \in Threads: WriteRelease(t)
    \/ \E t \in Threads: UpreadRelease(t)
    \/ \E t \in Threads: UpgradeBegin(t)
    \/ \E t \in Threads: UpgradeCommit(t)
    \/ \E t \in Threads: Downgrade(t)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A t \in Threads:
        /\ WF_vars(ReadRelease(t))
        /\ WF_vars(WriteRelease(t))
        /\ WF_vars(UpreadRelease(t))
        /\ WF_vars(ReadAcquire(t))
        /\ WF_vars(WriteAcquire(t))
        /\ WF_vars(UpreadAcquire(t))
        /\ WF_vars(UpgradeCommit(t))

====