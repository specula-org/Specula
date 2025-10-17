---- MODULE rwmutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS T

Kinds == {"R","W","U"}

VARIABLES
  mode,
  rc,
  wr,
  up,
  bu,
  Q,
  wake

vars == << mode, rc, wr, up, bu, Q, wake >>

TypeOK ==
  /\ mode \in [T -> {"Idle","R","W","U","Upgrading"}]
  /\ rc \in Nat
  /\ wr \in BOOLEAN
  /\ up \in BOOLEAN
  /\ bu \in BOOLEAN
  /\ Q \in Seq([tid: T, kind: Kinds])
  /\ wake \in {"none","one","all"}
  /\ \A t \in T: Cardinality({ i \in 1..Len(Q) : Q[i].tid = t }) \in {0,1}
  /\ \A i \in 1..Len(Q): mode[Q[i].tid] = "Idle"
  /\ Cardinality({ t \in T: mode[t] = "W" }) \in {0,1}
  /\ wr <=> \E t \in T: mode[t] = "W"
  /\ up <=> \E t \in T: mode[t] \in {"U","Upgrading"}
  /\ bu <=> \E t \in T: mode[t] = "Upgrading"
  /\ rc = Cardinality({ t \in T: mode[t] = "R" })

Init ==
  /\ mode = [t \in T |-> "Idle"]
  /\ rc = 0
  /\ wr = FALSE
  /\ up = FALSE
  /\ bu = FALSE
  /\ Q = << >>
  /\ wake = "none"

InQ(q, t) == \E i \in 1..Len(q): q[i].tid = t

HeadIs(q, k) == Len(q) > 0 /\ q[1].kind = k

HeadTid(q) == q[1].tid

LeadCount(q) ==
  LET S == { n \in 0..Len(q) : \A i \in 1..n: q[i].kind = "R" }
  IN CHOOSE m \in S : \A n \in S : n <= m

LeadingReaderTids(q) == { q[i].tid : i \in 1..LeadCount(q) }

Index(q, t) == CHOOSE i \in 1..Len(q) : q[i].tid = t

RemoveAt(q, i) == q[1..i-1] \o q[i+1..Len(q)]

CanRead == ~wr /\ ~bu
CanWrite == ~wr /\ ~up /\ rc = 0
CanUpread == ~wr /\ ~up

Read(t) ==
  /\ t \in T
  /\ mode[t] = "Idle"
  /\ ~InQ(Q, t)
  /\ Q' = Q \o << [tid |-> t, kind |-> "R"] >>
  /\ UNCHANGED << mode, rc, wr, up, bu, wake >>

Write(t) ==
  /\ t \in T
  /\ mode[t] = "Idle"
  /\ ~InQ(Q, t)
  /\ Q' = Q \o << [tid |-> t, kind |-> "W"] >>
  /\ UNCHANGED << mode, rc, wr, up, bu, wake >>

Upread(t) ==
  /\ t \in T
  /\ mode[t] = "Idle"
  /\ ~InQ(Q, t)
  /\ Q' = Q \o << [tid |-> t, kind |-> "U"] >>
  /\ UNCHANGED << mode, rc, wr, up, bu, wake >>

QAcquireR(t) ==
  /\ t \in T
  /\ mode[t] = "Idle"
  /\ InQ(Q, t)
  /\ CanRead
  /\ IF wake = "all"
        THEN /\ t \in LeadingReaderTids(Q)
             /\ Q' = RemoveAt(Q, Index(Q, t))
        ELSE /\ HeadIs(Q, "R") /\ HeadTid(Q) = t
             /\ Q' = RemoveAt(Q, 1)
  /\ mode' = [mode EXCEPT ![t] = "R"]
  /\ rc' = rc + 1
  /\ IF wake = "one" THEN wake' = "none" ELSE wake' = wake
  /\ UNCHANGED << wr, up, bu >>

QAcquireW(t) ==
  /\ t \in T
  /\ mode[t] = "Idle"
  /\ HeadIs(Q, "W")
  /\ HeadTid(Q) = t
  /\ CanWrite
  /\ Q' = RemoveAt(Q, 1)
  /\ mode' = [mode EXCEPT ![t] = "W"]
  /\ wr' = TRUE
  /\ IF wake = "one" THEN wake' = "none" ELSE wake' = wake
  /\ UNCHANGED << rc, up, bu >>

QAcquireU(t) ==
  /\ t \in T
  /\ mode[t] = "Idle"
  /\ HeadIs(Q, "U")
  /\ HeadTid(Q) = t
  /\ CanUpread
  /\ Q' = RemoveAt(Q, 1)
  /\ mode' = [mode EXCEPT ![t] = "U"]
  /\ up' = TRUE
  /\ IF wake = "one" THEN wake' = "none" ELSE wake' = wake
  /\ UNCHANGED << rc, wr, bu >>

UpgradeBegin(t) ==
  /\ t \in T
  /\ mode[t] = "U"
  /\ up
  /\ ~bu
  /\ bu' = TRUE
  /\ mode' = [mode EXCEPT ![t] = "Upgrading"]
  /\ UNCHANGED << rc, wr, up, Q, wake >>

UpgradeCommit(t) ==
  /\ t \in T
  /\ mode[t] = "Upgrading"
  /\ up
  /\ bu
  /\ rc = 0
  /\ ~wr
  /\ wr' = TRUE
  /\ up' = FALSE
  /\ bu' = FALSE
  /\ mode' = [mode EXCEPT ![t] = "W"]
  /\ wake' = "all"
  /\ UNCHANGED << rc, Q >>

Downgrade(t) ==
  /\ t \in T
  /\ mode[t] = "W"
  /\ wr
  /\ up' = TRUE
  /\ wr' = FALSE
  /\ mode' = [mode EXCEPT ![t] = "U"]
  /\ wake' = "all"
  /\ UNCHANGED << rc, bu, Q >>

ReleaseR(t) ==
  /\ t \in T
  /\ mode[t] = "R"
  /\ mode' = [mode EXCEPT ![t] = "Idle"]
  /\ rc' = rc - 1
  /\ IF rc' = 0 THEN wake' = "one" ELSE wake' = wake
  /\ UNCHANGED << wr, up, bu, Q >>

ReleaseW(t) ==
  /\ t \in T
  /\ mode[t] = "W"
  /\ mode' = [mode EXCEPT ![t] = "Idle"]
  /\ wr' = FALSE
  /\ wake' = "all"
  /\ UNCHANGED << rc, up, bu, Q >>

ReleaseU(t) ==
  /\ t \in T
  /\ mode[t] = "U"
  /\ up
  /\ ~bu
  /\ mode' = [mode EXCEPT ![t] = "Idle"]
  /\ up' = FALSE
  /\ wake' = "all"
  /\ UNCHANGED << rc, wr, bu, Q >>

Next ==
  \E t \in T:
    Read(t)
    \/ Write(t)
    \/ Upread(t)
    \/ QAcquireR(t)
    \/ QAcquireW(t)
    \/ QAcquireU(t)
    \/ UpgradeBegin(t)
    \/ UpgradeCommit(t)
    \/ Downgrade(t)
    \/ ReleaseR(t)
    \/ ReleaseW(t)
    \/ ReleaseU(t)

Fairness ==
  /\ \A t \in T: WF_vars(QAcquireR(t))
  /\ \A t \in T: WF_vars(QAcquireW(t))
  /\ \A t \in T: WF_vars(QAcquireU(t))
  /\ \A t \in T: WF_vars(UpgradeCommit(t))

Spec == Init /\ [][Next]_vars /\ Fairness

====