---- MODULE rwmutex ----
EXTENDS TLC, Sequences, Naturals, FiniteSets

CONSTANT Proc

VARIABLES lock, Q, mode, WSig

ModeSet == {"Idle","WaitRead","Reading","WaitWrite","Writing","WaitUpread","Upreading","Upgrading"}
OpSet == {"Read","Write","Upread"}
WakeSet == {"None","One","All"}

TypeOK ==
  /\ lock \in [writer: {0,1}, upread: {0,1}, being: {0,1}, readers: Nat]
  /\ Q \in Seq([p: Proc, kind: OpSet])
  /\ mode \in [Proc -> ModeSet]
  /\ WSig \in WakeSet

CanRead == lock.writer = 0 /\ lock.being = 0
CanWrite == lock.writer = 0 /\ lock.upread = 0 /\ lock.readers = 0 /\ lock.being = 0
CanUpread == lock.writer = 0 /\ lock.upread = 0

IsEnqueued(p) == \E i \in 1..Len(Q): Q[i].p = p

ReadersPrefixLen(qq) ==
  IF Len(qq) = 0 THEN 0
  ELSE LET I == { i \in 1..Len(qq) : \A j \in 1..i: qq[j].kind = "Read" }
       IN IF I = {} THEN 0 ELSE CHOOSE m \in I: \A n \in I: m >= n

DropN(qq, n) == IF n >= Len(qq) THEN <<>> ELSE SubSeq(qq, n+1, Len(qq))
TakeN(qq, n) == IF n = 0 THEN <<>> ELSE SubSeq(qq, 1, n)
PfxReadersSet(qq) == { qq[i].p : i \in 1..ReadersPrefixLen(qq) }

Init ==
  /\ lock = [writer |-> 0, upread |-> 0, being |-> 0, readers |-> 0]
  /\ Q = <<>>
  /\ mode = [p \in Proc |-> "Idle"]
  /\ WSig = "None"
  /\ TypeOK

ReadTryAcquire(p) ==
  /\ p \in Proc
  /\ mode[p] = "Idle"
  /\ CanRead
  /\ lock' = [lock EXCEPT !.readers = @ + 1]
  /\ mode' = [mode EXCEPT ![p] = "Reading"]
  /\ UNCHANGED << Q, WSig >>

ReadEnqueue(p) ==
  /\ p \in Proc
  /\ mode[p] = "Idle"
  /\ ~CanRead
  /\ ~IsEnqueued(p)
  /\ Q' = Append(Q, [p |-> p, kind |-> "Read"])
  /\ mode' = [mode EXCEPT ![p] = "WaitRead"]
  /\ UNCHANGED << lock, WSig >>

ReadRelease(p) ==
  /\ p \in Proc
  /\ mode[p] = "Reading"
  /\ lock.readers > 0
  /\ lock' = [lock EXCEPT !.readers = @ - 1]
  /\ WSig' =
      IF lock.readers = 1
      THEN IF WSig = "All" THEN "All" ELSE "One"
      ELSE WSig
  /\ mode' = [mode EXCEPT ![p] = "Idle"]
  /\ UNCHANGED Q

WriteTryAcquire(p) ==
  /\ p \in Proc
  /\ mode[p] = "Idle"
  /\ CanWrite
  /\ lock' = [lock EXCEPT !.writer = 1]
  /\ mode' = [mode EXCEPT ![p] = "Writing"]
  /\ UNCHANGED << Q, WSig >>

WriteEnqueue(p) ==
  /\ p \in Proc
  /\ mode[p] = "Idle"
  /\ ~CanWrite
  /\ ~IsEnqueued(p)
  /\ Q' = Append(Q, [p |-> p, kind |-> "Write"])
  /\ mode' = [mode EXCEPT ![p] = "WaitWrite"]
  /\ UNCHANGED << lock, WSig >>

WriteRelease(p) ==
  /\ p \in Proc
  /\ mode[p] = "Writing"
  /\ lock.writer = 1
  /\ lock' = [lock EXCEPT !.writer = 0]
  /\ WSig' = "All"
  /\ mode' = [mode EXCEPT ![p] = "Idle"]
  /\ UNCHANGED Q

UpreadTryAcquire(p) ==
  /\ p \in Proc
  /\ mode[p] = "Idle"
  /\ CanUpread
  /\ lock' = [lock EXCEPT !.upread = 1]
  /\ mode' = [mode EXCEPT ![p] = "Upreading"]
  /\ UNCHANGED << Q, WSig >>

UpreadEnqueue(p) ==
  /\ p \in Proc
  /\ mode[p] = "Idle"
  /\ ~CanUpread
  /\ ~IsEnqueued(p)
  /\ Q' = Append(Q, [p |-> p, kind |-> "Upread"])
  /\ mode' = [mode EXCEPT ![p] = "WaitUpread"]
  /\ UNCHANGED << lock, WSig >>

UpreadRelease(p) ==
  /\ p \in Proc
  /\ mode[p] = "Upreading"
  /\ lock.upread = 1
  /\ lock' = [lock EXCEPT !.upread = 0]
  /\ WSig' =
      IF lock.readers = 0 /\ lock.writer = 0 /\ lock.being = 0 /\ lock.upread = 1
      THEN "All" ELSE WSig
  /\ mode' = [mode EXCEPT ![p] = "Idle"]
  /\ UNCHANGED Q

UpgradeStart(p) ==
  /\ p \in Proc
  /\ mode[p] = "Upreading"
  /\ lock.upread = 1
  /\ lock.being = 0
  /\ lock' = [lock EXCEPT !.being = 1]
  /\ mode' = [mode EXCEPT ![p] = "Upgrading"]
  /\ UNCHANGED << Q, WSig >>

UpgradeFinish(p) ==
  /\ p \in Proc
  /\ mode[p] = "Upgrading"
  /\ lock.upread = 1
  /\ lock.readers = 0
  /\ lock.writer = 0
  /\ lock.being = 1
  /\ lock' = [lock EXCEPT !.writer = 1, !.being = 0, !.upread = 0]
  /\ mode' = [mode EXCEPT ![p] = "Writing"]
  /\ UNCHANGED << Q, WSig >>

Downgrade(p) ==
  /\ p \in Proc
  /\ mode[p] = "Writing"
  /\ lock.writer = 1
  /\ lock' = [lock EXCEPT !.writer = 0, !.upread = 1]
  /\ mode' = [mode EXCEPT ![p] = "Upreading"]
  /\ WSig' = "All"
  /\ UNCHANGED Q

GrantOne ==
  /\ WSig = "One"
  /\ Len(Q) > 0
  /\ LET e == Q[1] IN
     IF e.kind = "Read" /\ CanRead
        THEN /\ lock' = [lock EXCEPT !.readers = @ + 1]
             /\ mode' = [mode EXCEPT ![e.p] = "Reading"]
             /\ Q' = DropN(Q, 1)
             /\ WSig' = "None"
     ELSE IF e.kind = "Write" /\ CanWrite
        THEN /\ lock' = [lock EXCEPT !.writer = 1]
             /\ mode' = [mode EXCEPT ![e.p] = "Writing"]
             /\ Q' = DropN(Q, 1)
             /\ WSig' = "None"
     ELSE IF e.kind = "Upread" /\ CanUpread
        THEN /\ lock' = [lock EXCEPT !.upread = 1]
             /\ mode' = [mode EXCEPT ![e.p] = "Upreading"]
             /\ Q' = DropN(Q, 1)
             /\ WSig' = "None"
     ELSE FALSE

GrantAll ==
  /\ WSig = "All"
  /\ Len(Q) > 0
  /\ LET e == Q[1] IN
     IF e.kind = "Read" /\ CanRead
        THEN LET k == ReadersPrefixLen(Q),
                 ps == PfxReadersSet(Q)
             IN /\ k > 0
                /\ lock' = [lock EXCEPT !.readers = @ + k]
                /\ mode' = [ p \in Proc |-> IF p \in ps THEN "Reading" ELSE mode[p] ]
                /\ Q' = DropN(Q, k)
                /\ WSig' = "None"
     ELSE IF e.kind = "Write" /\ CanWrite
        THEN /\ lock' = [lock EXCEPT !.writer = 1]
             /\ mode' = [mode EXCEPT ![e.p] = "Writing"]
             /\ Q' = DropN(Q, 1)
             /\ WSig' = "None"
     ELSE IF e.kind = "Upread" /\ CanUpread
        THEN /\ lock' = [lock EXCEPT !.upread = 1]
             /\ mode' = [mode EXCEPT ![e.p] = "Upreading"]
             /\ Q' = DropN(Q, 1)
             /\ WSig' = "None"
     ELSE FALSE

Next ==
  \/ \E p \in Proc: ReadTryAcquire(p)
  \/ \E p \in Proc: ReadEnqueue(p)
  \/ \E p \in Proc: ReadRelease(p)
  \/ \E p \in Proc: WriteTryAcquire(p)
  \/ \E p \in Proc: WriteEnqueue(p)
  \/ \E p \in Proc: WriteRelease(p)
  \/ \E p \in Proc: UpreadTryAcquire(p)
  \/ \E p \in Proc: UpreadEnqueue(p)
  \/ \E p \in Proc: UpreadRelease(p)
  \/ \E p \in Proc: UpgradeStart(p)
  \/ \E p \in Proc: UpgradeFinish(p)
  \/ \E p \in Proc: Downgrade(p)
  \/ GrantOne
  \/ GrantAll

Vars == << lock, Q, mode, WSig >>

Spec ==
  Init /\ [][Next]_Vars /\ WF_Vars(Next)

====