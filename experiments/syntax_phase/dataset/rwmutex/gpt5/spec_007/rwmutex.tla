---- MODULE rwmutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANT THREADS

Kinds == {"Read","Write","Upread"}
Modes == {"Idle","Reading","Writing","Upreading","Upgrading","WaitingRead","WaitingWrite","WaitingUpread"}

VARIABLES lock, mode, waitQ, awake

TypeOK ==
  /\ lock \in [writer: BOOLEAN, upread: BOOLEAN, upgrading: BOOLEAN, readers: Nat]
  /\ mode \in [THREADS -> Modes]
  /\ waitQ \in Seq([tid: THREADS, kind: Kinds])
  /\ \A i,j \in 1..Len(waitQ) : i # j => waitQ[i].tid # waitQ[j].tid
  /\ awake \subseteq { waitQ[i].tid : i \in 1..Len(waitQ) }

Init ==
  /\ lock = [writer |-> FALSE, upread |-> FALSE, upgrading |-> FALSE, readers |-> 0]
  /\ mode = [t \in THREADS |-> "Idle"]
  /\ waitQ = << >>
  /\ awake = {}

WaitersSet(q) == { q[i].tid : i \in 1..Len(q) }

InQ(q, t) == \E i \in 1..Len(q) : q[i].tid = t

Pos(q, t) ==
  IF InQ(q, t) THEN CHOOSE i \in 1..Len(q) : q[i].tid = t ELSE 0

AllReadersBefore(q, t) ==
  LET i == Pos(q, t) IN \A j \in 1..(i-1) : q[j].kind = "Read"

RemoveAt(q, i) ==
  SubSeq(q, 1, i-1) \o SubSeq(q, i+1, Len(q))

RemoveTid(q, t) ==
  IF InQ(q, t) THEN RemoveAt(q, Pos(q, t)) ELSE q

HeadTid(q) == q[1].tid

ReadTryAcquire(t) ==
  /\ mode[t] = "Idle"
  /\ ~lock.writer /\ ~lock.upgrading
  /\ lock' = [lock EXCEPT !.readers = @ + 1]
  /\ mode' = [mode EXCEPT ![t] = "Reading"]
  /\ UNCHANGED << waitQ, awake >>

ReadEnqueue(t) ==
  /\ mode[t] = "Idle"
  /\ ~(~lock.writer /\ ~lock.upgrading)
  /\ ~InQ(waitQ, t)
  /\ waitQ' = waitQ \o << [tid |-> t, kind |-> "Read"] >>
  /\ mode' = [mode EXCEPT ![t] = "WaitingRead"]
  /\ UNCHANGED << lock, awake >>

AcquireWaitingRead(t) ==
  /\ mode[t] = "WaitingRead"
  /\ InQ(waitQ, t) /\ t \in awake
  /\ ~lock.writer /\ ~lock.upgrading
  /\ AllReadersBefore(waitQ, t)
  /\ lock' = [lock EXCEPT !.readers = @ + 1]
  /\ waitQ' = RemoveTid(waitQ, t)
  /\ awake' = awake \ {t}
  /\ mode' = [mode EXCEPT ![t] = "Reading"]

WriteTryAcquire(t) ==
  /\ mode[t] = "Idle"
  /\ ~lock.writer /\ ~lock.upread /\ ~lock.upgrading /\ lock.readers = 0
  /\ lock' = [lock EXCEPT !.writer = TRUE]
  /\ mode' = [mode EXCEPT ![t] = "Writing"]
  /\ UNCHANGED << waitQ, awake >>

WriteEnqueue(t) ==
  /\ mode[t] = "Idle"
  /\ ~(~lock.writer /\ ~lock.upread /\ ~lock.upgrading /\ lock.readers = 0)
  /\ ~InQ(waitQ, t)
  /\ waitQ' = waitQ \o << [tid |-> t, kind |-> "Write"] >>
  /\ mode' = [mode EXCEPT ![t] = "WaitingWrite"]
  /\ UNCHANGED << lock, awake >>

AcquireWaitingWrite(t) ==
  /\ mode[t] = "WaitingWrite"
  /\ Len(waitQ) > 0 /\ HeadTid(waitQ) = t
  /\ t \in awake
  /\ ~lock.writer /\ ~lock.upread /\ ~lock.upgrading /\ lock.readers = 0
  /\ lock' = [lock EXCEPT !.writer = TRUE]
  /\ waitQ' = SubSeq(waitQ, 2, Len(waitQ))
  /\ awake' = awake \ {t}
  /\ mode' = [mode EXCEPT ![t] = "Writing"]

UpreadTryAcquire(t) ==
  /\ mode[t] = "Idle"
  /\ ~lock.writer /\ ~lock.upread
  /\ lock' = [lock EXCEPT !.upread = TRUE]
  /\ mode' = [mode EXCEPT ![t] = "Upreading"]
  /\ UNCHANGED << waitQ, awake >>

UpreadEnqueue(t) ==
  /\ mode[t] = "Idle"
  /\ ~(~lock.writer /\ ~lock.upread)
  /\ ~InQ(waitQ, t)
  /\ waitQ' = waitQ \o << [tid |-> t, kind |-> "Upread"] >>
  /\ mode' = [mode EXCEPT ![t] = "WaitingUpread"]
  /\ UNCHANGED << lock, awake >>

AcquireWaitingUpread(t) ==
  /\ mode[t] = "WaitingUpread"
  /\ Len(waitQ) > 0 /\ HeadTid(waitQ) = t
  /\ t \in awake
  /\ ~lock.writer /\ ~lock.upread
  /\ lock' = [lock EXCEPT !.upread = TRUE]
  /\ waitQ' = SubSeq(waitQ, 2, Len(waitQ))
  /\ awake' = awake \ {t}
  /\ mode' = [mode EXCEPT ![t] = "Upreading"]

ReleaseRead(t) ==
  /\ mode[t] = "Reading"
  /\ lock.readers > 0
  /\ LET newReaders == lock.readers - 1 IN
     /\ lock' = [lock EXCEPT !.readers = newReaders]
     /\ awake' =
          IF newReaders = 0 THEN
             IF Len(waitQ) = 0 THEN {}
             ELSE { HeadTid(waitQ) }
          ELSE awake
  /\ mode' = [mode EXCEPT ![t] = "Idle"]
  /\ UNCHANGED waitQ

ReleaseWrite(t) ==
  /\ mode[t] = "Writing"
  /\ lock.writer
  /\ lock' = [lock EXCEPT !.writer = FALSE]
  /\ awake' = WaitersSet(waitQ)
  /\ mode' = [mode EXCEPT ![t] = "Idle"]
  /\ UNCHANGED waitQ

ReleaseUpread(t) ==
  /\ mode[t] = "Upreading"
  /\ ~lock.upgrading
  /\ lock.upread
  /\ lock' = [lock EXCEPT !.upread = FALSE]
  /\ awake' =
       IF (~lock.writer /\ lock.readers = 0) THEN WaitersSet(waitQ) ELSE awake
  /\ mode' = [mode EXCEPT ![t] = "Idle"]
  /\ UNCHANGED waitQ

UpgradeStart(t) ==
  /\ mode[t] = "Upreading"
  /\ ~lock.upgrading
  /\ lock' = [lock EXCEPT !.upgrading = TRUE]
  /\ mode' = [mode EXCEPT ![t] = "Upgrading"]
  /\ UNCHANGED << waitQ, awake >>

UpgradeFinish(t) ==
  /\ mode[t] = "Upgrading"
  /\ lock.readers = 0
  /\ lock' = [lock EXCEPT !.writer = TRUE, !.upgrading = FALSE, !.upread = FALSE]
  /\ mode' = [mode EXCEPT ![t] = "Writing"]
  /\ UNCHANGED << waitQ, awake >>

Downgrade(t) ==
  /\ mode[t] = "Writing"
  /\ lock.writer
  /\ lock' = [lock EXCEPT !.writer = FALSE, !.upread = TRUE]
  /\ awake' = WaitersSet(waitQ)
  /\ mode' = [mode EXCEPT ![t] = "Upreading"]
  /\ UNCHANGED waitQ

Next ==
  \E t \in THREADS :
    \/ ReadTryAcquire(t)
    \/ ReadEnqueue(t)
    \/ AcquireWaitingRead(t)
    \/ WriteTryAcquire(t)
    \/ WriteEnqueue(t)
    \/ AcquireWaitingWrite(t)
    \/ UpreadTryAcquire(t)
    \/ UpreadEnqueue(t)
    \/ AcquireWaitingUpread(t)
    \/ ReleaseRead(t)
    \/ ReleaseWrite(t)
    \/ ReleaseUpread(t)
    \/ UpgradeStart(t)
    \/ UpgradeFinish(t)
    \/ Downgrade(t)

Vars == << lock, mode, waitQ, awake >>

Spec ==
  /\ Init
  /\ [][Next]_Vars
  /\ \A t \in THREADS :
       /\ WF_Vars(AcquireWaitingRead(t))
       /\ WF_Vars(AcquireWaitingWrite(t))
       /\ WF_Vars(AcquireWaitingUpread(t))
       /\ WF_Vars(UpgradeFinish(t))

====