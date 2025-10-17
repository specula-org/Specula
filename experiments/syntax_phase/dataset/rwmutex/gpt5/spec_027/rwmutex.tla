---- MODULE raftkvs ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Threads, None

VARIABLES readers, writer, up, upgrading, waitQ, activeReaders, activeWriter, activeUp, ready

vars == <<readers, writer, up, upgrading, waitQ, activeReaders, activeWriter, activeUp, ready>>

Kinds == {"R","W","U"}

CanRead == ~writer /\ ~upgrading
CanWrite == readers = 0 /\ ~up /\ ~upgrading
CanUpread == ~writer /\ ~up

InQueue(q, t) == \E i \in 1..Len(q): q[i].id = t

Index(q, t) == IF \E j \in 1..Len(q): q[j].id = t THEN CHOOSE j \in 1..Len(q): q[j].id = t ELSE 0
RemoveById(q, t) ==
  LET i == Index(q, t) IN
    IF i = 0 THEN q ELSE SubSeq(q, 1, i-1) \o SubSeq(q, i+1, Len(q)) \* minimal fix: use concatenation instead of Append to avoid nested sequences

FirstNonReader(q) ==
  IF Len(q) = 0 THEN 1
  ELSE IF \A i \in 1..Len(q): q[i].kind = "R" THEN Len(q) + 1
  ELSE CHOOSE i \in 1..Len(q): q[i].kind # "R" /\ \A j \in 1..i-1: q[j].kind = "R"

ReaderPrefixIds(q) == { q[i].id : i \in 1..(FirstNonReader(q)-1) }

AdmitSet(q) ==
  IF Len(q) = 0 THEN {}
  ELSE IF q[1].kind = "R" THEN ReaderPrefixIds(q) ELSE { q[1].id }

NotHolding(t) == ~(t \in activeReaders \/ activeWriter = t \/ activeUp = t)

Init ==
  /\ readers = 0
  /\ writer = FALSE
  /\ up = FALSE
  /\ upgrading = FALSE
  /\ waitQ = <<>>
  /\ activeReaders = {}
  /\ activeWriter = None
  /\ activeUp = None
  /\ ready = {}

EnqueueRead(t) ==
  /\ t \in Threads
  /\ NotHolding(t)
  /\ ~((Len(waitQ) = 0) /\ CanRead)
  /\ ~InQueue(waitQ, t)
  /\ waitQ' = Append(waitQ, [id |-> t, kind |-> "R"])
  /\ UNCHANGED <<readers, writer, up, upgrading, activeReaders, activeWriter, activeUp, ready>>

EnqueueWrite(t) ==
  /\ t \in Threads
  /\ NotHolding(t)
  /\ ~((Len(waitQ) = 0) /\ CanWrite)
  /\ ~InQueue(waitQ, t)
  /\ waitQ' = Append(waitQ, [id |-> t, kind |-> "W"])
  /\ UNCHANGED <<readers, writer, up, upgrading, activeReaders, activeWriter, activeUp, ready>>

EnqueueUpread(t) ==
  /\ t \in Threads
  /\ NotHolding(t)
  /\ ~((Len(waitQ) = 0) /\ CanUpread)
  /\ ~InQueue(waitQ, t)
  /\ waitQ' = Append(waitQ, [id |-> t, kind |-> "U"])
  /\ UNCHANGED <<readers, writer, up, upgrading, activeReaders, activeWriter, activeUp, ready>>

ReadAcquire(t) ==
  /\ t \in Threads
  /\ NotHolding(t)
  /\ (
       (Len(waitQ) = 0 /\ CanRead /\ ~InQueue(waitQ, t))
       \/
       (t \in ready /\ (\E i \in 1..Len(waitQ): waitQ[i].id = t /\ waitQ[i].kind = "R") /\ CanRead)
     )
  /\ readers' = readers + 1
  /\ activeReaders' = activeReaders \cup {t}
  /\ waitQ' = RemoveById(waitQ, t)
  /\ ready' = ready \ {t}
  /\ UNCHANGED <<writer, up, upgrading, activeWriter, activeUp>>

WriteAcquire(t) ==
  /\ t \in Threads
  /\ NotHolding(t)
  /\ (
       (Len(waitQ) = 0 /\ CanWrite /\ ~InQueue(waitQ, t))
       \/
       (t \in ready /\ (\E i \in 1..Len(waitQ): waitQ[i].id = t /\ waitQ[i].kind = "W") /\ CanWrite)
     )
  /\ writer' = TRUE
  /\ activeWriter' = t
  /\ waitQ' = RemoveById(waitQ, t)
  /\ ready' = ready \ {t}
  /\ UNCHANGED <<readers, up, upgrading, activeReaders, activeUp>>

UpreadAcquire(t) ==
  /\ t \in Threads
  /\ NotHolding(t)
  /\ (
       (Len(waitQ) = 0 /\ CanUpread /\ ~InQueue(waitQ, t))
       \/
       (t \in ready /\ (\E i \in 1..Len(waitQ): waitQ[i].id = t /\ waitQ[i].kind = "U") /\ CanUpread)
     )
  /\ up' = TRUE
  /\ activeUp' = t
  /\ waitQ' = RemoveById(waitQ, t)
  /\ ready' = ready \ {t}
  /\ UNCHANGED <<readers, writer, upgrading, activeReaders, activeWriter>>

ReadRelease(t) ==
  /\ t \in Threads
  /\ t \in activeReaders
  /\ readers' = readers - 1
  /\ activeReaders' = activeReaders \ {t}
  /\ waitQ' = waitQ
  /\ ready' = IF readers' = 0 /\ Len(waitQ) > 0 THEN ready \cup {waitQ[1].id} ELSE ready
  /\ UNCHANGED <<writer, up, upgrading, activeWriter, activeUp>>

WriteRelease(t) ==
  /\ t \in Threads
  /\ activeWriter = t
  /\ writer = TRUE
  /\ writer' = FALSE
  /\ activeWriter' = None
  /\ waitQ' = waitQ
  /\ ready' = ready \cup AdmitSet(waitQ)
  /\ UNCHANGED <<readers, up, upgrading, activeReaders, activeUp>>

UpreadRelease(t) ==
  /\ t \in Threads
  /\ activeUp = t
  /\ up = TRUE
  /\ upgrading = FALSE
  /\ up' = FALSE
  /\ activeUp' = None
  /\ waitQ' = waitQ
  /\ ready' = ready \cup AdmitSet(waitQ)
  /\ UNCHANGED <<readers, writer, upgrading, activeReaders, activeWriter>>

UpgradeAttempt(t) ==
  /\ t \in Threads
  /\ activeUp = t
  /\ up = TRUE
  /\ writer = FALSE
  /\ upgrading = FALSE
  /\ upgrading' = TRUE
  /\ UNCHANGED <<readers, writer, up, waitQ, activeReaders, activeWriter, activeUp, ready>>

UpgradeCommit(t) ==
  /\ t \in Threads
  /\ activeUp = t
  /\ up = TRUE
  /\ upgrading = TRUE
  /\ readers = 0
  /\ writer = FALSE
  /\ writer' = TRUE
  /\ up' = FALSE
  /\ upgrading' = FALSE
  /\ activeWriter' = t
  /\ activeUp' = None
  /\ UNCHANGED <<readers, waitQ, activeReaders, ready>>

Downgrade(t) ==
  /\ t \in Threads
  /\ activeWriter = t
  /\ writer = TRUE
  /\ up = FALSE
  /\ writer' = FALSE
  /\ up' = TRUE
  /\ activeWriter' = None
  /\ activeUp' = t
  /\ waitQ' = waitQ
  /\ ready' = ready \cup AdmitSet(waitQ)
  /\ UNCHANGED <<readers, upgrading, activeReaders>>

Next ==
  \/ \E t \in Threads: EnqueueRead(t)
  \/ \E t \in Threads: EnqueueWrite(t)
  \/ \E t \in Threads: EnqueueUpread(t)
  \/ \E t \in Threads: ReadAcquire(t)
  \/ \E t \in Threads: WriteAcquire(t)
  \/ \E t \in Threads: UpreadAcquire(t)
  \/ \E t \in Threads: ReadRelease(t)
  \/ \E t \in Threads: WriteRelease(t)
  \/ \E t \in Threads: UpreadRelease(t)
  \/ \E t \in Threads: UpgradeAttempt(t)
  \/ \E t \in Threads: UpgradeCommit(t)
  \/ \E t \in Threads: Downgrade(t)

Fairness ==
  /\ \A t \in Threads: WF_vars(ReadAcquire(t))
  /\ \A t \in Threads: WF_vars(WriteAcquire(t))
  /\ \A t \in Threads: WF_vars(UpreadAcquire(t))
  /\ \A t \in Threads: WF_vars(UpgradeCommit(t))

Spec == Init /\ [][Next]_vars /\ Fairness

====