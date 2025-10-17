---- MODULE raftkvs ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS
    Threads,
    NoThread,
    R, W, U,
    Idle, One, All

GATES == {Idle, One, All}
Kinds == {R, W, U}

VARIABLES
    Lock,
    ReadersHeld,
    WriterHeld,
    UpReaderHeld,
    Q,
    Gate

vars == << Lock, ReadersHeld, WriterHeld, UpReaderHeld, Q, Gate >>

Init ==
    /\ Lock = [ writer |-> FALSE,
                upreader |-> FALSE,
                beingUpgraded |-> FALSE,
                readers |-> 0 ]
    /\ ReadersHeld = {}
    /\ WriterHeld = NoThread
    /\ UpReaderHeld = NoThread
    /\ Q = << >>
    /\ Gate = Idle

InQ(t) ==
    \E i \in 1..Len(Q): Q[i].t = t

HoldsNone(t) ==
    /\ ~(t \in ReadersHeld)
    /\ WriterHeld # t
    /\ UpReaderHeld # t

CanRead ==
    /\ ~Lock.writer
    /\ ~Lock.beingUpgraded

CanWrite ==
    /\ Lock.readers = 0
    /\ ~Lock.writer
    /\ ~Lock.upreader

CanUpread ==
    /\ ~Lock.writer
    /\ ~Lock.upreader

HeadX(q) == q[1]
Rest(q) == IF Len(q) = 0 THEN << >> ELSE SubSeq(q, 2, Len(q))

RECURSIVE Rpfx(_)
Rpfx(q) ==
    IF Len(q) = 0 \/ q[1].k # R
    THEN << >>
    ELSE << q[1] >> \o Rpfx(SubSeq(q, 2, Len(q)))

DropN(q, n) ==
    IF n = 0 THEN q
    ELSE IF n >= Len(q) THEN << >>
    ELSE SubSeq(q, n + 1, Len(q))

BatchThreads(s) ==
    { s[i].t : i \in 1..Len(s) }

ReadAcquire(t) ==
    /\ t \in Threads
    /\ HoldsNone(t)
    /\ ~InQ(t)
    /\ CanRead
    /\ Lock' = [Lock EXCEPT !.readers = @ + 1]
    /\ ReadersHeld' = ReadersHeld \cup {t}
    /\ UNCHANGED << WriterHeld, UpReaderHeld, Q, Gate >>

ReadEnqueue(t) ==
    /\ t \in Threads
    /\ HoldsNone(t)
    /\ ~InQ(t)
    /\ ~CanRead
    /\ Q' = Append(Q, [t |-> t, k |-> R])
    /\ UNCHANGED << Lock, ReadersHeld, WriterHeld, UpReaderHeld, Gate >>

ReadRelease(t) ==
    /\ t \in Threads
    /\ t \in ReadersHeld
    /\ LET r1 == Lock.readers - 1 IN
       /\ Lock' = [Lock EXCEPT !.readers = r1]
       /\ ReadersHeld' = ReadersHeld \ {t}
       /\ Gate' = IF r1 = 0 THEN One ELSE Gate
    /\ UNCHANGED << WriterHeld, UpReaderHeld, Q >>

WriteAcquire(t) ==
    /\ t \in Threads
    /\ HoldsNone(t)
    /\ ~InQ(t)
    /\ CanWrite
    /\ Lock' = [Lock EXCEPT !.writer = TRUE]
    /\ WriterHeld' = t
    /\ UNCHANGED << ReadersHeld, UpReaderHeld, Q, Gate, Lock.beingUpgraded, Lock.readers, Lock.upreader >>

WriteEnqueue(t) ==
    /\ t \in Threads
    /\ HoldsNone(t)
    /\ ~InQ(t)
    /\ ~CanWrite
    /\ Q' = Append(Q, [t |-> t, k |-> W])
    /\ UNCHANGED << Lock, ReadersHeld, WriterHeld, UpReaderHeld, Gate >>

WriteRelease(t) ==
    /\ t \in Threads
    /\ WriterHeld = t
    /\ Lock' = [Lock EXCEPT !.writer = FALSE]
    /\ WriterHeld' = NoThread
    /\ Gate' = All
    /\ UNCHANGED << ReadersHeld, UpReaderHeld, Q, Lock.upreader, Lock.beingUpgraded, Lock.readers >>

UpreadAcquire(t) ==
    /\ t \in Threads
    /\ HoldsNone(t)
    /\ ~InQ(t)
    /\ CanUpread
    /\ Lock' = [Lock EXCEPT !.upreader = TRUE]
    /\ UpReaderHeld' = t
    /\ UNCHANGED << ReadersHeld, WriterHeld, Q, Gate, Lock.writer, Lock.beingUpgraded, Lock.readers >>

UpreadEnqueue(t) ==
    /\ t \in Threads
    /\ HoldsNone(t)
    /\ ~InQ(t)
    /\ ~CanUpread
    /\ Q' = Append(Q, [t |-> t, k |-> U])
    /\ UNCHANGED << Lock, ReadersHeld, WriterHeld, UpReaderHeld, Gate >>

UpreadRelease(t) ==
    /\ t \in Threads
    /\ UpReaderHeld = t
    /\ ~Lock.beingUpgraded
    /\ Lock' = [Lock EXCEPT !.upreader = FALSE]
    /\ UpReaderHeld' = NoThread
    /\ Gate' = All
    /\ UNCHANGED << ReadersHeld, WriterHeld, Q, Lock.writer, Lock.beingUpgraded, Lock.readers >>

UpgradeStart(t) ==
    /\ t \in Threads
    /\ UpReaderHeld = t
    /\ ~Lock.beingUpgraded
    /\ Lock' = [Lock EXCEPT !.beingUpgraded = TRUE]
    /\ UNCHANGED << ReadersHeld, WriterHeld, UpReaderHeld, Q, Gate, Lock.writer, Lock.upreader, Lock.readers >>

UpgradeFinish(t) ==
    /\ t \in Threads
    /\ UpReaderHeld = t
    /\ Lock.beingUpgraded
    /\ Lock.readers = 0
    /\ ~Lock.writer
    /\ Lock' = [Lock EXCEPT !.beingUpgraded = FALSE,
                         !.upreader = FALSE,
                         !.writer = TRUE]
    /\ WriterHeld' = t
    /\ UpReaderHeld' = NoThread
    /\ UNCHANGED << ReadersHeld, Q, Gate, Lock.readers >>

Downgrade(t) ==
    /\ t \in Threads
    /\ WriterHeld = t
    /\ Lock' = [Lock EXCEPT !.writer = FALSE,
                         !.upreader = TRUE,
                         !.beingUpgraded = FALSE]
    /\ UpReaderHeld' = t
    /\ WriterHeld' = NoThread
    /\ Gate' = All
    /\ UNCHANGED << ReadersHeld, Q, Lock.readers >>

AdmitHeadWU ==
    /\ Gate \in {One, All}
    /\ Len(Q) >= 1
    /\ LET req == Q[1] IN
       (\/ /\ req.k = W
          /\ CanWrite
          /\ Lock' = [Lock EXCEPT !.writer = TRUE]
          /\ WriterHeld' = req.t
          /\ Q' = Rest(Q)
          /\ Gate' = Idle
          /\ UNCHANGED << ReadersHeld, UpReaderHeld, Lock.upreader, Lock.beingUpgraded, Lock.readers >>
        \/ /\ req.k = U
          /\ CanUpread
          /\ Lock' = [Lock EXCEPT !.upreader = TRUE]
          /\ UpReaderHeld' = req.t
          /\ Q' = Rest(Q)
          /\ Gate' = Idle
          /\ UNCHANGED << ReadersHeld, WriterHeld, Lock.writer, Lock.beingUpgraded, Lock.readers >>)

AdmitOneReader ==
    /\ Gate = One
    /\ Len(Q) >= 1
    /\ Q[1].k = R
    /\ CanRead
    /\ Lock' = [Lock EXCEPT !.readers = @ + 1]
    /\ ReadersHeld' = ReadersHeld \cup { Q[1].t }
    /\ Q' = Rest(Q)
    /\ Gate' = Idle
    /\ UNCHANGED << WriterHeld, UpReaderHeld, Lock.writer, Lock.upreader, Lock.beingUpgraded >>

AdmitReadersPrefix ==
    /\ Gate = All
    /\ Len(Q) >= 1
    /\ Q[1].k = R
    /\ CanRead
    /\ LET batch == Rpfx(Q) IN
       /\ Lock' = [Lock EXCEPT !.readers = @ + Len(batch)]
       /\ ReadersHeld' = ReadersHeld \cup BatchThreads(batch)
       /\ Q' = DropN(Q, Len(batch))
       /\ Gate' = Idle
       /\ UNCHANGED << WriterHeld, UpReaderHeld, Lock.writer, Lock.upreader, Lock.beingUpgraded >>

ReadReq(t) ==
    ReadAcquire(t) \/ ReadEnqueue(t)

WriteReq(t) ==
    WriteAcquire(t) \/ WriteEnqueue(t)

UpreadReq(t) ==
    UpreadAcquire(t) \/ UpreadEnqueue(t)

Next ==
    \/ \E t \in Threads: ReadReq(t)
    \/ \E t \in Threads: WriteReq(t)
    \/ \E t \in Threads: UpreadReq(t)
    \/ \E t \in Threads: ReadRelease(t)
    \/ \E t \in Threads: WriteRelease(t)
    \/ \E t \in Threads: UpreadRelease(t)
    \/ \E t \in Threads: UpgradeStart(t)
    \/ \E t \in Threads: UpgradeFinish(t)
    \/ \E t \in Threads: Downgrade(t)
    \/ AdmitHeadWU
    \/ AdmitOneReader
    \/ AdmitReadersPrefix

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A t \in Threads:
        /\ WF_vars(ReadRelease(t))
        /\ WF_vars(WriteRelease(t))
        /\ WF_vars(UpreadRelease(t))
        /\ WF_vars(UpgradeStart(t))
        /\ WF_vars(UpgradeFinish(t))
        /\ WF_vars(Downgrade(t))
    /\ WF_vars(AdmitHeadWU)
    /\ WF_vars(AdmitOneReader)
    /\ WF_vars(AdmitReadersPrefix)

====