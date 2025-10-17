---- MODULE rwmutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Proc

Kinds == {"Read","Write","Upread"}
Modes == {"Idle","Read","Write","Upread","Upgrading"}

Req == [pid: Proc, kind: Kinds]
Lock == [writer: BOOLEAN, upread: BOOLEAN, upgrading: BOOLEAN, readers: Nat]

IsEmpty(q) == Len(q) = 0
Head(q) == q[1]
Tail(q) == SubSeq(q, 2, Len(q))
QPids(q) == { q[i].pid : i \in 1..Len(q) }

CanRead(l) == ~l.writer /\ ~l.upgrading
CanWrite(l) == ~l.writer /\ ~l.upread /\ l.readers = 0
CanUpread(l) == ~l.writer /\ ~l.upread

VARIABLES lock, mode, queue, awake

Vars == << lock, mode, queue, awake >>

TypeOK ==
  /\ lock \in Lock
  /\ mode \in [Proc -> Modes]
  /\ queue \in Seq(Req)
  /\ awake \subseteq Proc

Init ==
  /\ lock = [writer |-> FALSE, upread |-> FALSE, upgrading |-> FALSE, readers |-> 0]
  /\ mode = [p \in Proc |-> "Idle"]
  /\ queue = <<>>
  /\ awake = {}

StartRead(p) ==
  /\ p \in Proc
  /\ mode[p] = "Idle"
  /\ CanRead(lock)
  /\ lock' = [lock EXCEPT !.readers = @ + 1]
  /\ mode' = [mode EXCEPT ![p] = "Read"]
  /\ UNCHANGED << queue, awake >>

QueueRead(p) ==
  /\ p \in Proc
  /\ mode[p] = "Idle"
  /\ ~CanRead(lock)
  /\ queue' = Append(queue, [pid |-> p, kind |-> "Read"])
  /\ UNCHANGED << lock, mode, awake >>

AcquireHeadRead(p) ==
  /\ p \in Proc
  /\ ~IsEmpty(queue)
  /\ Head(queue).kind = "Read"
  /\ Head(queue).pid = p
  /\ p \in awake
  /\ CanRead(lock)
  /\ lock' = [lock EXCEPT !.readers = @ + 1]
  /\ mode' = [mode EXCEPT ![p] = "Read"]
  /\ queue' = Tail(queue)
  /\ awake' = awake \ {p}

StartWrite(p) ==
  /\ p \in Proc
  /\ mode[p] = "Idle"
  /\ CanWrite(lock)
  /\ lock' = [lock EXCEPT !.writer = TRUE]
  /\ mode' = [mode EXCEPT ![p] = "Write"]
  /\ UNCHANGED << queue, awake, >>

QueueWrite(p) ==
  /\ p \in Proc
  /\ mode[p] = "Idle"
  /\ ~CanWrite(lock)
  /\ queue' = Append(queue, [pid |-> p, kind |-> "Write"])
  /\ UNCHANGED << lock, mode, awake >>

AcquireHeadWrite(p) ==
  /\ p \in Proc
  /\ ~IsEmpty(queue)
  /\ Head(queue).kind = "Write"
  /\ Head(queue).pid = p
  /\ p \in awake
  /\ CanWrite(lock)
  /\ lock' = [lock EXCEPT !.writer = TRUE]
  /\ mode' = [mode EXCEPT ![p] = "Write"]
  /\ queue' = Tail(queue)
  /\ awake' = awake \ {p}

StartUpread(p) ==
  /\ p \in Proc
  /\ mode[p] = "Idle"
  /\ CanUpread(lock)
  /\ lock' = [lock EXCEPT !.upread = TRUE]
  /\ mode' = [mode EXCEPT ![p] = "Upread"]
  /\ UNCHANGED << queue, awake >>

QueueUpread(p) ==
  /\ p \in Proc
  /\ mode[p] = "Idle"
  /\ ~CanUpread(lock)
  /\ queue' = Append(queue, [pid |-> p, kind |-> "Upread"])
  /\ UNCHANGED << lock, mode, awake >>

AcquireHeadUpread(p) ==
  /\ p \in Proc
  /\ ~IsEmpty(queue)
  /\ Head(queue).kind = "Upread"
  /\ Head(queue).pid = p
  /\ p \in awake
  /\ CanUpread(lock)
  /\ lock' = [lock EXCEPT !.upread = TRUE]
  /\ mode' = [mode EXCEPT ![p] = "Upread"]
  /\ queue' = Tail(queue)
  /\ awake' = awake \ {p}

UpgradeStart(p) ==
  /\ p \in Proc
  /\ mode[p] = "Upread"
  /\ ~lock.upgrading
  /\ lock' = [lock EXCEPT !.upgrading = TRUE]
  /\ mode' = [mode EXCEPT ![p] = "Upgrading"]
  /\ UNCHANGED << queue, awake >>

UpgradeComplete(p) ==
  /\ p \in Proc
  /\ mode[p] = "Upgrading"
  /\ lock.upgrading
  /\ lock.readers = 0
  /\ ~lock.writer
  /\ lock' = [lock EXCEPT !.writer = TRUE, !.upgrading = FALSE, !.upread = FALSE]
  /\ mode' = [mode EXCEPT ![p] = "Write"]
  /\ UNCHANGED << queue, awake >>

Downgrade(p) ==
  /\ p \in Proc
  /\ mode[p] = "Write"
  /\ lock' = [lock EXCEPT !.upread = TRUE, !.writer = FALSE]
  /\ mode' = [mode EXCEPT ![p] = "Upread"]
  /\ awake' = awake \cup QPids(queue)
  /\ UNCHANGED queue

ReleaseRead(p) ==
  /\ p \in Proc
  /\ mode[p] = "Read"
  /\ mode' = [mode EXCEPT ![p] = "Idle"]
  /\ lock' = [lock EXCEPT !.readers = @ - 1]
  /\ awake' =
      IF lock.readers = 1 /\ ~IsEmpty(queue)
      THEN awake \cup { Head(queue).pid }
      ELSE awake
  /\ UNCHANGED queue

ReleaseWrite(p) ==
  /\ p \in Proc
  /\ mode[p] = "Write"
  /\ mode' = [mode EXCEPT ![p] = "Idle"]
  /\ lock' = [lock EXCEPT !.writer = FALSE]
  /\ awake' = awake \cup QPids(queue)
  /\ UNCHANGED queue

ReleaseUpread(p) ==
  /\ p \in Proc
  /\ mode[p] = "Upread"
  /\ ~lock.upgrading
  /\ mode' = [mode EXCEPT ![p] = "Idle"]
  /\ lock' = [lock EXCEPT !.upread = FALSE]
  /\ awake' =
      IF lock.readers = 0
      THEN awake \cup QPids(queue)
      ELSE awake
  /\ UNCHANGED queue

Next ==
  \E p \in Proc:
    StartRead(p) \/ QueueRead(p) \/ AcquireHeadRead(p) \/
    StartWrite(p) \/ QueueWrite(p) \/ AcquireHeadWrite(p) \/
    StartUpread(p) \/ QueueUpread(p) \/ AcquireHeadUpread(p) \/
    UpgradeStart(p) \/ UpgradeComplete(p) \/ Downgrade(p) \/
    ReleaseRead(p) \/ ReleaseWrite(p) \/ ReleaseUpread(p)

DoAcquire ==
  \E p \in Proc: AcquireHeadRead(p) \/ AcquireHeadWrite(p) \/ AcquireHeadUpread(p)

DoRelease ==
  \E p \in Proc: ReleaseRead(p) \/ ReleaseWrite(p) \/ ReleaseUpread(p)

DoUpgradeComplete ==
  \E p \in Proc: UpgradeComplete(p)

Spec ==
  Init /\ [][Next]_Vars /\ WF_Vars(DoAcquire) /\ WF_Vars(DoRelease) /\ WF_Vars(DoUpgradeComplete)

====