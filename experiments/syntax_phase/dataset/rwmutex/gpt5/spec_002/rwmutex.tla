---- MODULE rwmutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Threads, NoThread

WRITER == 8
UPGRADEABLE_READER == 4
BEING_UPGRADED == 2

READER == 1

StatusVals == {"Idle","Reading","Writing","Upread","Upgrading","WaitingRead","WaitingWrite","WaitingUpread"}

VARIABLES lock, readers, writer, upreader, upgrading, status, Q, Woken

TypeOK ==
  /\ lock \in Nat
  /\ readers \subseteq Threads
  /\ writer \in Threads \cup {NoThread}
  /\ upreader \in Threads \cup {NoThread}
  /\ upgrading \in BOOLEAN
  /\ status \in [Threads -> StatusVals]
  /\ Q \in Seq(Threads)
  /\ Woken \subseteq { Q[i] : i \in 1..Len(Q) }

EncodeLock(rs, wr, ur, upg) ==
  (IF wr = NoThread THEN 0 ELSE WRITER)
  + (IF ur = NoThread THEN 0 ELSE UPGRADEABLE_READER)
  + (IF upg THEN BEING_UPGRADED ELSE 0)
  + Cardinality(rs)

Elems(s) == { s[i] : i \in 1..Len(s) }
NotInSeq(s, t) == ~(t \in Elems(s))
Head(s) == s[1]
Tail(s) == SubSeq(s, 2, Len(s))
DropPrefix(s, n) == SubSeq(s, n+1, Len(s))

WaitingKind(t) ==
  IF status[t] = "WaitingRead" THEN "Read"
  ELSE IF status[t] = "WaitingWrite" THEN "Write"
  ELSE IF status[t] = "WaitingUpread" THEN "Upread"
  ELSE "None"

ReadHeadLen ==
  IF Len(Q) = 0 \/ WaitingKind(Q[1]) # "Read" THEN 0
  ELSE Max({ i \in 1..Len(Q) : \A j \in 1..i : WaitingKind(Q[j]) = "Read" })

HeadReadThreads ==
  { Q[i] : i \in 1..ReadHeadLen }

CanReadNow == (writer = NoThread) /\ ~upgrading
CanWriteNow == (writer = NoThread) /\ (upreader = NoThread) /\ ~upgrading /\ (readers = {})
CanUpreadNow == (writer = NoThread) /\ (upreader = NoThread)

Init ==
  /\ lock = 0
  /\ readers = {}
  /\ writer = NoThread
  /\ upreader = NoThread
  /\ upgrading = FALSE
  /\ status \in [Threads -> {"Idle"}]
  /\ Q = << >>
  /\ Woken = {}

ReadFastPath ==
  \E t \in Threads:
    /\ status[t] = "Idle"
    /\ Len(Q) = 0
    /\ CanReadNow
    /\ readers' = readers \cup {t}
    /\ writer' = writer
    /\ upreader' = upreader
    /\ upgrading' = upgrading
    /\ status' = [status EXCEPT ![t] = "Reading"]
    /\ Q' = Q
    /\ Woken' = Woken
    /\ lock' = EncodeLock(readers', writer', upreader', upgrading')

WriteFastPath ==
  \E t \in Threads:
    /\ status[t] = "Idle"
    /\ Len(Q) = 0
    /\ CanWriteNow
    /\ readers' = readers
    /\ writer' = t
    /\ upreader' = upreader
    /\ upgrading' = upgrading
    /\ status' = [status EXCEPT ![t] = "Writing"]
    /\ Q' = Q
    /\ Woken' = Woken
    /\ lock' = EncodeLock(readers', writer', upreader', upgrading')

UpreadFastPath ==
  \E t \in Threads:
    /\ status[t] = "Idle"
    /\ Len(Q) = 0
    /\ CanUpreadNow
    /\ readers' = readers
    /\ writer' = writer
    /\ upreader' = t
    /\ upgrading' = upgrading
    /\ status' = [status EXCEPT ![t] = "Upread"]
    /\ Q' = Q
    /\ Woken' = Woken
    /\ lock' = EncodeLock(readers', writer', upreader', upgrading')

ReadEnqueue ==
  \E t \in Threads:
    /\ status[t] = "Idle"
    /\ ~(Len(Q) = 0 /\ CanReadNow)
    /\ NotInSeq(Q, t)
    /\ readers' = readers
    /\ writer' = writer
    /\ upreader' = upreader
    /\ upgrading' = upgrading
    /\ status' = [status EXCEPT ![t] = "WaitingRead"]
    /\ Q' = Append(Q, t)
    /\ Woken' = Woken
    /\ lock' = EncodeLock(readers', writer', upreader', upgrading')

WriteEnqueue ==
  \E t \in Threads:
    /\ status[t] = "Idle"
    /\ ~(Len(Q) = 0 /\ CanWriteNow)
    /\ NotInSeq(Q, t)
    /\ readers' = readers
    /\ writer' = writer
    /\ upreader' = upreader
    /\ upgrading' = upgrading
    /\ status' = [status EXCEPT ![t] = "WaitingWrite"]
    /\ Q' = Append(Q, t)
    /\ Woken' = Woken
    /\ lock' = EncodeLock(readers', writer', upreader', upgrading')

UpreadEnqueue ==
  \E t \in Threads:
    /\ status[t] = "Idle"
    /\ ~(Len(Q) = 0 /\ CanUpreadNow)
    /\ NotInSeq(Q, t)
    /\ readers' = readers
    /\ writer' = writer
    /\ upreader' = upreader
    /\ upgrading' = upgrading
    /\ status' = [status EXCEPT ![t] = "WaitingUpread"]
    /\ Q' = Append(Q, t)
    /\ Woken' = Woken
    /\ lock' = EncodeLock(readers', writer', upreader', upgrading')

HeadReadAcquireOne ==
  \E t \in Threads:
    /\ Len(Q) > 0
    /\ Q[1] = t
    /\ status[t] = "WaitingRead"
    /\ t \in Woken
    /\ CanReadNow
    /\ readers' = readers \cup {t}
    /\ writer' = writer
    /\ upreader' = upreader
    /\ upgrading' = upgrading
    /\ status' = [status EXCEPT ![t] = "Reading"]
    /\ Q' = Tail(Q)
    /\ Woken' = Woken \ {t}
    /\ lock' = EncodeLock(readers', writer', upreader', upgrading')

HeadReadBatchAcquireAll ==
  LET n == ReadHeadLen IN
  /\ n >= 1
  /\ CanReadNow
  /\ \A i \in 1..n : Q[i] \in Woken
  /\ readers' = readers \cup HeadReadThreads
  /\ writer' = writer
  /\ upreader' = upreader
  /\ upgrading' = upgrading
  /\ status' = [ t \in Threads |-> IF t \in HeadReadThreads THEN "Reading" ELSE status[t] ]
  /\ Q' = DropPrefix(Q, n)
  /\ Woken' = Woken \ HeadReadThreads
  /\ lock' = EncodeLock(readers', writer', upreader', upgrading')

HeadWriteAcquire ==
  \E t \in Threads:
    /\ Len(Q) > 0
    /\ Q[1] = t
    /\ status[t] = "WaitingWrite"
    /\ t \in Woken
    /\ CanWriteNow
    /\ readers' = readers
    /\ writer' = t
    /\ upreader' = upreader
    /\ upgrading' = upgrading
    /\ status' = [status EXCEPT ![t] = "Writing"]
    /\ Q' = Tail(Q)
    /\ Woken' = Woken \ {t}
    /\ lock' = EncodeLock(readers', writer', upreader', upgrading')

HeadUpreadAcquire ==
  \E t \in Threads:
    /\ Len(Q) > 0
    /\ Q[1] = t
    /\ status[t] = "WaitingUpread"
    /\ t \in Woken
    /\ CanUpreadNow
    /\ readers' = readers
    /\ writer' = writer
    /\ upreader' = t
    /\ upgrading' = upgrading
    /\ status' = [status EXCEPT ![t] = "Upread"]
    /\ Q' = Tail(Q)
    /\ Woken' = Woken \ {t}
    /\ lock' = EncodeLock(readers', writer', upreader', upgrading')

ReadRelease ==
  \E t \in Threads:
    /\ status[t] = "Reading"
    /\ readers' = readers \ {t}
    /\ writer' = writer
    /\ upreader' = upreader
    /\ upgrading' = upgrading
    /\ status' = [status EXCEPT ![t] = "Idle"]
    /\ Q' = Q
    /\ Woken' =
         IF readers' = {} /\ Len(Q) > 0
         THEN Woken \cup { Q[1] }
         ELSE Woken
    /\ lock' = EncodeLock(readers', writer', upreader', upgrading')

WriteRelease ==
  \E t \in Threads:
    /\ status[t] = "Writing"
    /\ writer = t
    /\ readers' = readers
    /\ writer' = NoThread
    /\ upreader' = upreader
    /\ upgrading' = upgrading
    /\ status' = [status EXCEPT ![t] = "Idle"]
    /\ Q' = Q
    /\ Woken' = Woken \cup Elems(Q)
    /\ lock' = EncodeLock(readers', writer', upreader', upgrading')

UpreadRelease ==
  \E t \in Threads:
    /\ status[t] = "Upread"
    /\ upreader = t
    /\ ~upgrading
    /\ readers' = readers
    /\ writer' = writer
    /\ upreader' = NoThread
    /\ upgrading' = FALSE
    /\ status' = [status EXCEPT ![t] = "Idle"]
    /\ Q' = Q
    /\ Woken' =
         IF (readers = {}) /\ (writer = NoThread) /\ (~upgrading)
         THEN Woken \cup Elems(Q)
         ELSE Woken
    /\ lock' = EncodeLock(readers', writer', upreader', upgrading')

Downgrade ==
  \E t \in Threads:
    /\ status[t] = "Writing"
    /\ writer = t
    /\ upreader = NoThread
    /\ readers' = readers
    /\ writer' = NoThread
    /\ upreader' = t
    /\ upgrading' = FALSE
    /\ status' = [status EXCEPT ![t] = "Upread"]
    /\ Q' = Q
    /\ Woken' = Woken
    /\ lock' = EncodeLock(readers', writer', upreader', upgrading')

UpgradeBegin ==
  \E t \in Threads:
    /\ status[t] = "Upread"
    /\ upreader = t
    /\ ~upgrading
    /\ readers' = readers
    /\ writer' = writer
    /\ upreader' = upreader
    /\ upgrading' = TRUE
    /\ status' = [status EXCEPT ![t] = "Upgrading"]
    /\ Q' = Q
    /\ Woken' = Woken
    /\ lock' = EncodeLock(readers', writer', upreader', upgrading')

TryUpgrade ==
  \E t \in Threads:
    /\ status[t] = "Upgrading"
    /\ upreader = t
    /\ upgrading
    /\ writer = NoThread
    /\ readers = {}
    /\ readers' = readers
    /\ writer' = t
    /\ upreader' = upreader
    /\ upgrading' = FALSE
    /\ status' = [status EXCEPT ![t] = "Writing"]
    /\ Q' = Q
    /\ Woken' = Woken
    /\ lock' = EncodeLock(readers', writer', upreader', upgrading')

Next ==
  \/ ReadFastPath
  \/ WriteFastPath
  \/ UpreadFastPath
  \/ ReadEnqueue
  \/ WriteEnqueue
  \/ UpreadEnqueue
  \/ HeadReadAcquireOne
  \/ HeadReadBatchAcquireAll
  \/ HeadWriteAcquire
  \/ HeadUpreadAcquire
  \/ ReadRelease
  \/ WriteRelease
  \/ UpreadRelease
  \/ Downgrade
  \/ UpgradeBegin
  \/ TryUpgrade

vars == << lock, readers, writer, upreader, upgrading, status, Q, Woken >>

Spec ==
  Init
  /\ TypeOK
  /\ [][Next]_vars
  /\ WF_vars(HeadReadAcquireOne)
  /\ WF_vars(HeadReadBatchAcquireAll)
  /\ WF_vars(HeadWriteAcquire)
  /\ WF_vars(HeadUpreadAcquire)
  /\ WF_vars(TryUpgrade)

====