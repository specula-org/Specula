---- MODULE rwmutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Threads, Null

ASSUME Null \notin Threads

Kinds == {"read", "write", "upread"}

VARIABLES
  lock,
  Q,
  Readers,
  Writer,
  UpReader,
  permitted

Vars == << lock, Q, Readers, Writer, UpReader, permitted >>

TypeOK ==
  /\ lock \in [writer: BOOLEAN, upg: BOOLEAN, upgrading: BOOLEAN, rc: Nat]
  /\ Q \in Seq([t: Threads, kind: Kinds])
  /\ Readers \subseteq Threads
  /\ Writer \in Threads \cup {Null}
  /\ UpReader \in Threads \cup {Null}
  /\ permitted \subseteq Threads

Init ==
  /\ lock = [writer |-> FALSE, upg |-> FALSE, upgrading |-> FALSE, rc |-> 0]
  /\ Q = << >>
  /\ Readers = {}
  /\ Writer = Null
  /\ UpReader = Null
  /\ permitted = {}

Head(q) == q[1]
Tail(q) == SubSeq(q, 2, Len(q))
AllQueued(q) == { q[i].t : i \in 1..Len(q) }
NotQueued(t) == \A i \in 1..Len(Q): Q[i].t # t
Req(t, k) == [t |-> t, kind |-> k]

HeadIsRead == Len(Q) > 0 /\ Head(Q).kind = "read"
PrefixIdxs(q) == { i \in 1..Len(q) : \A k \in 1..i: q[k].kind = "read" }
PrefixReadersSet(q) == { q[i].t : i \in PrefixIdxs(q) }
IndexOf(q, t) == CHOOSE i \in 1..Len(q) : q[i].t = t
RemoveAt(q, i) == SubSeq(q, 1, i-1) \o SubSeq(q, i+1, Len(q))

CanRead == ~lock.writer /\ ~lock.upgrading
CanWrite == lock.rc = 0 /\ ~lock.writer /\ ~lock.upg /\ ~lock.upgrading
CanUpread == ~lock.writer /\ ~lock.upg
CanUpgrade == lock.upg /\ lock.rc = 0 /\ ~lock.writer

NotHolding(t) == t \notin Readers /\ t # Writer /\ t # UpReader

Read(t) ==
  /\ t \in Threads
  /\ NotHolding(t)
  /\ NotQueued(t)
  /\ IF Len(Q) = 0 /\ CanRead
     THEN /\ lock' = [lock EXCEPT !.rc = @ + 1]
          /\ Readers' = Readers \cup {t}
          /\ UNCHANGED << Q, Writer, UpReader, permitted >>
     ELSE /\ Q' = Append(Q, Req(t, "read"))
          /\ UNCHANGED << lock, Readers, Writer, UpReader, permitted >>

Write(t) ==
  /\ t \in Threads
  /\ NotHolding(t)
  /\ NotQueued(t)
  /\ IF Len(Q) = 0 /\ CanWrite
     THEN /\ lock' = [lock EXCEPT !.writer = TRUE]
          /\ Writer' = t
          /\ UNCHANGED << Q, Readers, UpReader, permitted >>
     ELSE /\ Q' = Append(Q, Req(t, "write"))
          /\ UNCHANGED << lock, Readers, Writer, UpReader, permitted >>

Upread(t) ==
  /\ t \in Threads
  /\ NotHolding(t)
  /\ NotQueued(t)
  /\ IF Len(Q) = 0 /\ CanUpread
     THEN /\ lock' = [lock EXCEPT !.upg = TRUE]
          /\ UpReader' = t
          /\ UNCHANGED << Q, Readers, Writer, permitted >>
     ELSE /\ Q' = Append(Q, Req(t, "upread"))
          /\ UNCHANGED << lock, Readers, Writer, UpReader, permitted >>

ReadAcquireFromPermitted(t) ==
  /\ t \in Threads
  /\ t \in permitted
  /\ Len(Q) > 0 /\ HeadIsRead
  /\ t \in PrefixReadersSet(Q)
  /\ NotHolding(t)
  /\ CanRead
  /\ LET i == CHOOSE j \in PrefixIdxs(Q) : Q[j].t = t
     IN  /\ Q' = RemoveAt(Q, i)
         /\ permitted' = permitted \ {t}
         /\ lock' = [lock EXCEPT !.rc = @ + 1]
         /\ Readers' = Readers \cup {t}
         /\ UNCHANGED << Writer, UpReader >>

WriteAcquireFromPermitted(t) ==
  /\ t \in Threads
  /\ t \in permitted
  /\ Len(Q) > 0 /\ Head(Q) = Req(t, "write")
  /\ NotHolding(t)
  /\ CanWrite
  /\ Q' = Tail(Q)
  /\ permitted' = permitted \ {t}
  /\ lock' = [lock EXCEPT !.writer = TRUE]
  /\ Writer' = t
  /\ UNCHANGED << Readers, UpReader >>

UpreadAcquireFromPermitted(t) ==
  /\ t \in Threads
  /\ t \in permitted
  /\ Len(Q) > 0 /\ Head(Q) = Req(t, "upread")
  /\ NotHolding(t)
  /\ CanUpread
  /\ Q' = Tail(Q)
  /\ permitted' = permitted \ {t}
  /\ lock' = [lock EXCEPT !.upg = TRUE]
  /\ UpReader' = t
  /\ UNCHANGED << Readers, Writer >>

ReadRelease(t) ==
  /\ t \in Threads
  /\ t \in Readers
  /\ Readers' = Readers \ {t}
  /\ lock' = [lock EXCEPT !.rc = @ - 1]
  /\ permitted' =
       IF lock'.rc = 0 /\ Len(Q) > 0
       THEN permitted \cup {Q[1].t}
       ELSE permitted
  /\ UNCHANGED << Q, Writer, UpReader >>

WriteRelease(t) ==
  /\ t \in Threads
  /\ Writer = t
  /\ Writer' = Null
  /\ lock' = [lock EXCEPT !.writer = FALSE]
  /\ permitted' = permitted \cup AllQueued(Q)
  /\ UNCHANGED << Q, Readers, UpReader >>

UpreadRelease(t) ==
  /\ t \in Threads
  /\ UpReader = t
  /\ ~lock.upgrading
  /\ UpReader' = Null
  /\ lock' = [lock EXCEPT !.upg = FALSE]
  /\ permitted' =
       IF lock.rc = 0
       THEN permitted \cup AllQueued(Q)
       ELSE permitted
  /\ UNCHANGED << Q, Readers, Writer >>

UpgradeStart(t) ==
  /\ t \in Threads
  /\ UpReader = t
  /\ ~lock.upgrading
  /\ lock' = [lock EXCEPT !.upgrading = TRUE]
  /\ UNCHANGED << Q, Readers, Writer, UpReader, permitted >>

UpgradeCommit(t) ==
  /\ t \in Threads
  /\ UpReader = t
  /\ lock.upgrading
  /\ CanUpgrade
  /\ lock' = [lock EXCEPT !.writer = TRUE, !.upg = FALSE, !.upgrading = FALSE]
  /\ Writer' = t
  /\ UpReader' = Null
  /\ UNCHANGED << Q, Readers, permitted >>

Downgrade(t) ==
  /\ t \in Threads
  /\ Writer = t
  /\ lock' = [lock EXCEPT !.writer = FALSE, !.upg = TRUE]
  /\ Writer' = Null
  /\ UpReader' = t
  /\ permitted' = permitted \cup AllQueued(Q)
  /\ UNCHANGED << Q, Readers >>

Skip == UNCHANGED Vars

Next ==
  \E t \in Threads:
    Read(t)
    \/ Write(t)
    \/ Upread(t)
    \/ ReadAcquireFromPermitted(t)
    \/ WriteAcquireFromPermitted(t)
    \/ UpreadAcquireFromPermitted(t)
    \/ ReadRelease(t)
    \/ WriteRelease(t)
    \/ UpreadRelease(t)
    \/ UpgradeStart(t)
    \/ UpgradeCommit(t)
    \/ Downgrade(t)
  \/ Skip

Spec ==
  Init
  /\ [][Next]_Vars
  /\ \A t \in Threads:
       WF_Vars(ReadAcquireFromPermitted(t))
       /\ WF_Vars(WriteAcquireFromPermitted(t))
       /\ WF_Vars(UpreadAcquireFromPermitted(t))
       /\ WF_Vars(UpgradeCommit(t))

====