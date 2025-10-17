---- MODULE rwmutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANT Threads

ASSUME Threads # {}

Kinds == {"Read","Write","Upread"}
Modes == {"None","Read","Write","Upread","Upgrading"}
Gates == {"Open","ReadPhase","WritePhase"}

VARIABLES lock, Q, Awake, Gate, mode

TypeOK ==
  /\ lock \in [rc: Nat, w: BOOLEAN, u: BOOLEAN, bg: BOOLEAN]
  /\ Q \in Seq([t: Threads, kind: Kinds])
  /\ Awake \subseteq { Q[i].t : i \in 1..Len(Q) }
  /\ Gate \in Gates
  /\ mode \in [Threads -> Modes]

Init ==
  /\ lock = [rc |-> 0, w |-> FALSE, u |-> FALSE, bg |-> FALSE]
  /\ Q = << >>
  /\ Awake = {}
  /\ Gate = "Open"
  /\ mode = [t \in Threads |-> "None"]

InQ(t) == \E i \in 1..Len(Q): Q[i].t = t
IndexOf(t) == CHOOSE i \in 1..Len(Q): Q[i].t = t
RemoveAt(s, i) == SubSeq(s, 1, i-1) \o SubSeq(s, i+1, Len(s))
PrefixNoWriter(i) == \A j \in 1..i: Q[j].kind # "Write"
AllQueued == { Q[i].t : i \in 1..Len(Q) }
HeadKind == IF Len(Q) = 0 THEN "Read" ELSE Q[1].kind
CanRead == ~lock.w /\ ~lock.bg
CanWrite == ~lock.w /\ ~lock.u /\ lock.rc = 0
CanUpread == ~lock.w /\ ~lock.u

ReadImmediate(t) ==
  /\ t \in Threads
  /\ mode[t] = "None"
  /\ ~InQ(t)
  /\ Len(Q) = 0
  /\ CanRead
  /\ mode' = [mode EXCEPT ![t] = "Read"]
  /\ lock' = [lock EXCEPT !.rc = @ + 1]
  /\ UNCHANGED << Q, Awake, Gate >>

WriteImmediate(t) ==
  /\ t \in Threads
  /\ mode[t] = "None"
  /\ ~InQ(t)
  /\ Len(Q) = 0
  /\ CanWrite
  /\ mode' = [mode EXCEPT ![t] = "Write"]
  /\ lock' = [lock EXCEPT !.w = TRUE]
  /\ UNCHANGED << Q, Awake, Gate >>

UpreadImmediate(t) ==
  /\ t \in Threads
  /\ mode[t] = "None"
  /\ ~InQ(t)
  /\ Len(Q) = 0
  /\ CanUpread
  /\ mode' = [mode EXCEPT ![t] = "Upread"]
  /\ lock' = [lock EXCEPT !.u = TRUE]
  /\ UNCHANGED << Q, Awake, Gate >>

EnqueueRead(t) ==
  /\ t \in Threads
  /\ mode[t] = "None"
  /\ ~InQ(t)
  /\ ~(Len(Q) = 0 /\ CanRead)
  /\ Q' = Q \o << [t |-> t, kind |-> "Read"] >>
  /\ UNCHANGED << lock, Awake, Gate, mode >>

EnqueueWrite(t) ==
  /\ t \in Threads
  /\ mode[t] = "None"
  /\ ~InQ(t)
  /\ ~(Len(Q) = 0 /\ CanWrite)
  /\ Q' = Q \o << [t |-> t, kind |-> "Write"] >>
  /\ UNCHANGED << lock, Awake, Gate, mode >>

EnqueueUpread(t) ==
  /\ t \in Threads
  /\ mode[t] = "None"
  /\ ~InQ(t)
  /\ ~(Len(Q) = 0 /\ CanUpread)
  /\ Q' = Q \o << [t |-> t, kind |-> "Upread"] >>
  /\ UNCHANGED << lock, Awake, Gate, mode >>

AcquireFromQueueRead(t) ==
  /\ t \in Threads
  /\ mode[t] = "None"
  /\ InQ(t)
  /\ t \in Awake
  /\ Gate = "ReadPhase"
  /\ CanRead
  /\ LET i == IndexOf(t) IN
       /\ PrefixNoWriter(i)
       /\ Q' = RemoveAt(Q, i)
  /\ mode' = [mode EXCEPT ![t] = "Read"]
  /\ lock' = [lock EXCEPT !.rc = @ + 1]
  /\ Awake' = Awake \ {t}
  /\ UNCHANGED Gate

AcquireFromQueueUpread(t) ==
  /\ t \in Threads
  /\ mode[t] = "None"
  /\ InQ(t)
  /\ t \in Awake
  /\ Gate = "ReadPhase"
  /\ CanUpread
  /\ ~lock.u
  /\ LET i == IndexOf(t) IN
       /\ PrefixNoWriter(i)
       /\ Q' = RemoveAt(Q, i)
  /\ mode' = [mode EXCEPT ![t] = "Upread"]
  /\ lock' = [lock EXCEPT !.u = TRUE]
  /\ Awake' = Awake \ {t}
  /\ UNCHANGED Gate

AcquireFromQueueWrite(t) ==
  /\ t \in Threads
  /\ mode[t] = "None"
  /\ InQ(t)
  /\ t \in Awake
  /\ Gate = "WritePhase"
  /\ Len(Q) > 0
  /\ Q[1].t = t
  /\ Q[1].kind = "Write"
  /\ CanWrite
  /\ Q' = RemoveAt(Q, 1)
  /\ mode' = [mode EXCEPT ![t] = "Write"]
  /\ lock' = [lock EXCEPT !.w = TRUE]
  /\ Awake' = Awake \ {t}
  /\ UNCHANGED Gate

ReleaseRead(t) ==
  /\ t \in Threads
  /\ mode[t] = "Read"
  /\ mode' = [mode EXCEPT ![t] = "None"]
  /\ LET newrc == lock.rc - 1 IN
       /\ lock' = [lock EXCEPT !.rc = newrc]
       /\ Awake' = IF newrc = 0 /\ Len(Q) > 0 THEN {Q[1].t} ELSE Awake
       /\ Gate' =
            IF newrc = 0 /\ Len(Q) > 0
            THEN IF Q[1].kind = "Write" THEN "WritePhase" ELSE "ReadPhase"
            ELSE Gate
  /\ UNCHANGED Q

ReleaseWrite(t) ==
  /\ t \in Threads
  /\ mode[t] = "Write"
  /\ mode' = [mode EXCEPT ![t] = "None"]
  /\ lock' = [lock EXCEPT !.w = FALSE]
  /\ Awake' = IF Len(Q) > 0 THEN AllQueued ELSE Awake
  /\ Gate' =
       IF Len(Q) > 0
       THEN IF Q[1].kind = "Write" THEN "WritePhase" ELSE "ReadPhase"
       ELSE "Open"
  /\ UNCHANGED Q

ReleaseUpread(t) ==
  /\ t \in Threads
  /\ mode[t] = "Upread"
  /\ mode' = [mode EXCEPT ![t] = "None"]
  /\ lock' = [lock EXCEPT !.u = FALSE]
  /\ Awake' = IF Len(Q) > 0 THEN AllQueued ELSE Awake
  /\ Gate' =
       IF Len(Q) > 0
       THEN IF Q[1].kind = "Write" THEN "WritePhase" ELSE "ReadPhase"
       ELSE "Open"
  /\ UNCHANGED Q

BeginUpgrade(t) ==
  /\ t \in Threads
  /\ mode[t] = "Upread"
  /\ ~lock.bg
  /\ mode' = [mode EXCEPT ![t] = "Upgrading"]
  /\ lock' = [lock EXCEPT !.bg = TRUE]
  /\ UNCHANGED << Q, Awake, Gate >>

UpgradeSuccess(t) ==
  /\ t \in Threads
  /\ mode[t] = "Upgrading"
  /\ lock.u
  /\ lock.bg
  /\ ~lock.w
  /\ lock.rc = 0
  /\ mode' = [mode EXCEPT ![t] = "Write"]
  /\ lock' = [lock EXCEPT !.w = TRUE, !.bg = FALSE, !.u = FALSE]
  /\ Awake' = IF Len(Q) > 0 THEN AllQueued ELSE Awake
  /\ Gate' =
       IF Len(Q) > 0
       THEN IF Q[1].kind = "Write" THEN "WritePhase" ELSE "ReadPhase"
       ELSE "Open"
  /\ UNCHANGED Q

Downgrade(t) ==
  /\ t \in Threads
  /\ mode[t] = "Write"
  /\ mode' = [mode EXCEPT ![t] = "Upread"]
  /\ lock' = [lock EXCEPT !.w = FALSE, !.u = TRUE]
  /\ Awake' = IF Len(Q) > 0 THEN AllQueued ELSE Awake
  /\ Gate' =
       IF Len(Q) > 0
       THEN IF Q[1].kind = "Write" THEN "WritePhase" ELSE "ReadPhase"
       ELSE "Open"
  /\ UNCHANGED Q

Next ==
  \/ \E t \in Threads: ReadImmediate(t)
  \/ \E t \in Threads: WriteImmediate(t)
  \/ \E t \in Threads: UpreadImmediate(t)
  \/ \E t \in Threads: EnqueueRead(t)
  \/ \E t \in Threads: EnqueueWrite(t)
  \/ \E t \in Threads: EnqueueUpread(t)
  \/ \E t \in Threads: AcquireFromQueueRead(t)
  \/ \E t \in Threads: AcquireFromQueueUpread(t)
  \/ \E t \in Threads: AcquireFromQueueWrite(t)
  \/ \E t \in Threads: ReleaseRead(t)
  \/ \E t \in Threads: ReleaseWrite(t)
  \/ \E t \in Threads: ReleaseUpread(t)
  \/ \E t \in Threads: BeginUpgrade(t)
  \/ \E t \in Threads: UpgradeSuccess(t)
  \/ \E t \in Threads: Downgrade(t)

Vars == << lock, Q, Awake, Gate, mode >>

Spec == Init /\ [][Next]_Vars /\ WF_Vars(Next)

====