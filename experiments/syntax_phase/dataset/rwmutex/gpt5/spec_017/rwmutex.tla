---- MODULE rwmutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANT Threads

Ops == {"R", "W", "U"}
Modes == {"I", "R", "W", "U", "U2W"}
ReqKinds == Ops \cup {"None"}

VARIABLES wr, up, bu, rc, waitQ, awake, mode, req

Vars == << wr, up, bu, rc, waitQ, awake, mode, req >>

Entry(th, op) == [th |-> th, op |-> op]

Head(q) == q[1]
Tail(q) == SubSeq(q, 2, Len(q))

QThreads(q) == { q[i].th : i \in 1..Len(q) }

InQ(q, t) == \E i \in 1..Len(q): q[i].th = t

TryReadOK == ~wr /\ ~bu
TryWriteOK == rc = 0 /\ ~wr /\ ~up /\ ~bu
TryUpreadOK == ~wr /\ ~up

TypeOK ==
  /\ wr \in BOOLEAN
  /\ up \in BOOLEAN
  /\ bu \in BOOLEAN
  /\ rc \in Nat
  /\ waitQ \in Seq([th: Threads, op: Ops])
  /\ awake \subseteq Threads
  /\ mode \in [Threads -> Modes]
  /\ req \in [Threads -> ReqKinds]

Init ==
  /\ wr = FALSE
  /\ up = FALSE
  /\ bu = FALSE
  /\ rc = 0
  /\ waitQ = << >>
  /\ awake = {}
  /\ mode \in [Threads -> {"I"}]
  /\ req \in [Threads -> {"None"}]
  /\ TypeOK

ReadImmediate(t) ==
  /\ t \in Threads
  /\ mode[t] = "I"
  /\ TryReadOK
  /\ rc' = rc + 1
  /\ mode' = [mode EXCEPT ![t] = "R"]
  /\ UNCHANGED << wr, up, bu, waitQ, awake, req >>

WriteImmediate(t) ==
  /\ t \in Threads
  /\ mode[t] = "I"
  /\ TryWriteOK
  /\ wr' = TRUE
  /\ mode' = [mode EXCEPT ![t] = "W"]
  /\ UNCHANGED << up, bu, rc, waitQ, awake, req >>

UpreadImmediate(t) ==
  /\ t \in Threads
  /\ mode[t] = "I"
  /\ TryUpreadOK
  /\ up' = TRUE
  /\ mode' = [mode EXCEPT ![t] = "U"]
  /\ UNCHANGED << wr, bu, rc, waitQ, awake, req >>

ReadEnqueue(t) ==
  /\ t \in Threads
  /\ mode[t] = "I"
  /\ req[t] = "None"
  /\ ~TryReadOK
  /\ ~InQ(waitQ, t)
  /\ t \notin awake
  /\ waitQ' = Append(waitQ, Entry(t, "R"))
  /\ req' = [req EXCEPT ![t] = "R"]
  /\ UNCHANGED << wr, up, bu, rc, awake, mode >>

WriteEnqueue(t) ==
  /\ t \in Threads
  /\ mode[t] = "I"
  /\ req[t] = "None"
  /\ ~TryWriteOK
  /\ ~InQ(waitQ, t)
  /\ t \notin awake
  /\ waitQ' = Append(waitQ, Entry(t, "W"))
  /\ req' = [req EXCEPT ![t] = "W"]
  /\ UNCHANGED << wr, up, bu, rc, awake, mode >>

UpreadEnqueue(t) ==
  /\ t \in Threads
  /\ mode[t] = "I"
  /\ req[t] = "None"
  /\ ~TryUpreadOK
  /\ ~InQ(waitQ, t)
  /\ t \notin awake
  /\ waitQ' = Append(waitQ, Entry(t, "U"))
  /\ req' = [req EXCEPT ![t] = "U"]
  /\ UNCHANGED << wr, up, bu, rc, awake, mode >>

AcquireAwakeRead(t) ==
  /\ t \in Threads
  /\ t \in awake
  /\ mode[t] = "I"
  /\ req[t] = "R"
  /\ TryReadOK
  /\ rc' = rc + 1
  /\ mode' = [mode EXCEPT ![t] = "R"]
  /\ awake' = awake \ {t}
  /\ req' = [req EXCEPT ![t] = "None"]
  /\ UNCHANGED << wr, up, bu, waitQ >>

AcquireAwakeWrite(t) ==
  /\ t \in Threads
  /\ t \in awake
  /\ mode[t] = "I"
  /\ req[t] = "W"
  /\ TryWriteOK
  /\ wr' = TRUE
  /\ mode' = [mode EXCEPT ![t] = "W"]
  /\ awake' = awake \ {t}
  /\ req' = [req EXCEPT ![t] = "None"]
  /\ UNCHANGED << up, bu, rc, waitQ >>

AcquireAwakeUpread(t) ==
  /\ t \in Threads
  /\ t \in awake
  /\ mode[t] = "I"
  /\ req[t] = "U"
  /\ TryUpreadOK
  /\ up' = TRUE
  /\ mode' = [mode EXCEPT ![t] = "U"]
  /\ awake' = awake \ {t}
  /\ req' = [req EXCEPT ![t] = "None"]
  /\ UNCHANGED << wr, bu, rc, waitQ >>

FailToAcquire(t) ==
  /\ t \in Threads
  /\ t \in awake
  /\ mode[t] = "I"
  /\ req[t] \in Ops
  /\ ( (req[t] = "R" /\ ~TryReadOK)
     \/ (req[t] = "W" /\ ~TryWriteOK)
     \/ (req[t] = "U" /\ ~TryUpreadOK) )
  /\ ~InQ(waitQ, t)
  /\ waitQ' = Append(waitQ, Entry(t, req[t]))
  /\ awake' = awake \ {t}
  /\ UNCHANGED << wr, up, bu, rc, mode, req >>

ReleaseRead(t) ==
  /\ t \in Threads
  /\ mode[t] = "R"
  /\ rc > 0
  /\ rc' = rc - 1
  /\ mode' = [mode EXCEPT ![t] = "I"]
  /\ IF rc' = 0 /\ Len(waitQ) > 0
     THEN /\ awake' = awake \cup { Head(waitQ).th }
          /\ waitQ' = Tail(waitQ)
     ELSE /\ awake' = awake
          /\ waitQ' = waitQ
  /\ UNCHANGED << wr, up, bu, req >>

ReleaseWrite(t) ==
  /\ t \in Threads
  /\ mode[t] = "W"
  /\ wr = TRUE
  /\ wr' = FALSE
  /\ mode' = [mode EXCEPT ![t] = "I"]
  /\ awake' = awake \cup QThreads(waitQ)
  /\ waitQ' = << >>
  /\ UNCHANGED << up, bu, rc, req >>

ReleaseUpread(t) ==
  /\ t \in Threads
  /\ mode[t] = "U"
  /\ up = TRUE
  /\ up' = FALSE
  /\ mode' = [mode EXCEPT ![t] = "I"]
  /\ awake' = awake \cup QThreads(waitQ)
  /\ waitQ' = << >>
  /\ UNCHANGED << wr, bu, rc, req >>

BeginUpgrade(t) ==
  /\ t \in Threads
  /\ mode[t] = "U"
  /\ ~bu
  /\ bu' = TRUE
  /\ mode' = [mode EXCEPT ![t] = "U2W"]
  /\ UNCHANGED << wr, up, rc, waitQ, awake, req >>

UpgradeCommit(t) ==
  /\ t \in Threads
  /\ mode[t] = "U2W"
  /\ rc = 0
  /\ wr' = TRUE
  /\ up' = FALSE
  /\ bu' = FALSE
  /\ mode' = [mode EXCEPT ![t] = "W"]
  /\ UNCHANGED << rc, waitQ, awake, req >>

Downgrade(t) ==
  /\ t \in Threads
  /\ mode[t] = "W"
  /\ wr = TRUE
  /\ ~up
  /\ wr' = FALSE
  /\ up' = TRUE
  /\ mode' = [mode EXCEPT ![t] = "U"]
  /\ UNCHANGED << bu, rc, waitQ, awake, req >>

Next ==
  \E t \in Threads:
    \/ ReadImmediate(t)
    \/ WriteImmediate(t)
    \/ UpreadImmediate(t)
    \/ ReadEnqueue(t)
    \/ WriteEnqueue(t)
    \/ UpreadEnqueue(t)
    \/ AcquireAwakeRead(t)
    \/ AcquireAwakeWrite(t)
    \/ AcquireAwakeUpread(t)
    \/ FailToAcquire(t)
    \/ ReleaseRead(t)
    \/ ReleaseWrite(t)
    \/ ReleaseUpread(t)
    \/ BeginUpgrade(t)
    \/ UpgradeCommit(t)
    \/ Downgrade(t)

Spec ==
  /\ Init
  /\ [][Next]_Vars
  /\ \A t \in Threads:
       /\ WF_Vars(AcquireAwakeRead(t))
       /\ WF_Vars(AcquireAwakeWrite(t))
       /\ WF_Vars(AcquireAwakeUpread(t))
       /\ WF_Vars(UpgradeCommit(t))

====