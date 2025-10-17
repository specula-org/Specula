---- MODULE rwmutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANT THREAD

Kinds == {"Read", "Write", "Upread"}

States == {
  "Idle",
  "WaitingRead",
  "WaitingWrite",
  "WaitingUpread",
  "HoldingRead",
  "HoldingWrite",
  "HoldingUpread",
  "Upgrading"
}

QElemSet ==
  { [t |-> t, kind |-> k, awake |-> a] : t \in THREAD, k \in Kinds, a \in BOOLEAN }

IsEmpty(q) == Len(q) = 0

Tail(q) == IF Len(q) = 0 THEN << >> ELSE SubSeq(q, 2, Len(q))

Enqueue(q, t, k) == Append(q, [t |-> t, kind |-> k, awake |-> FALSE])

WakeOne(q) ==
  IF Len(q) = 0 THEN q
  ELSE [ i \in 1..Len(q) |-> IF i = 1 THEN [t |-> q[1].t, kind |-> q[1].kind, awake |-> TRUE] ELSE q[i] ]

WakeAll(q) ==
  [ i \in 1..Len(q) |-> [t |-> q[i].t, kind |-> q[i].kind, awake |-> TRUE] ]

CanRead(lock) == ~lock.writer /\ ~lock.upgrading

CanWrite(lock) == ~lock.writer /\ ~lock.upread /\ ~lock.upgrading /\ lock.readers = 0

CanUpread(lock) == ~lock.writer /\ ~lock.upread

VARIABLES lock, queue, pc

vars == << lock, queue, pc >>

TypeOK ==
  /\ lock \in [writer: BOOLEAN, upread: BOOLEAN, upgrading: BOOLEAN, readers: Nat]
  /\ queue \in Seq(QElemSet)
  /\ pc \in [THREAD -> States]

Init ==
  /\ lock = [writer |-> FALSE, upread |-> FALSE, upgrading |-> FALSE, readers |-> 0]
  /\ queue = << >>
  /\ pc \in [THREAD -> "Idle"]

ReadImmediate(t) ==
  /\ pc[t] = "Idle"
  /\ IsEmpty(queue)
  /\ CanRead(lock)
  /\ pc' = [pc EXCEPT ![t] = "HoldingRead"]
  /\ lock' = [lock EXCEPT !.readers = lock.readers + 1]
  /\ UNCHANGED queue

ReadEnqueue(t) ==
  /\ pc[t] = "Idle"
  /\ ~(IsEmpty(queue) /\ CanRead(lock))
  /\ pc' = [pc EXCEPT ![t] = "WaitingRead"]
  /\ queue' = Enqueue(queue, t, "Read")
  /\ UNCHANGED lock

Read(t) == ReadImmediate(t) \/ ReadEnqueue(t)

WriteImmediate(t) ==
  /\ pc[t] = "Idle"
  /\ IsEmpty(queue)
  /\ CanWrite(lock)
  /\ pc' = [pc EXCEPT ![t] = "HoldingWrite"]
  /\ lock' = [lock EXCEPT !.writer = TRUE]
  /\ UNCHANGED queue

WriteEnqueue(t) ==
  /\ pc[t] = "Idle"
  /\ ~(IsEmpty(queue) /\ CanWrite(lock))
  /\ pc' = [pc EXCEPT ![t] = "WaitingWrite"]
  /\ queue' = Enqueue(queue, t, "Write")
  /\ UNCHANGED lock

Write(t) == WriteImmediate(t) \/ WriteEnqueue(t)

UpreadImmediate(t) ==
  /\ pc[t] = "Idle"
  /\ IsEmpty(queue)
  /\ CanUpread(lock)
  /\ pc' = [pc EXCEPT ![t] = "HoldingUpread"]
  /\ lock' = [lock EXCEPT !.upread = TRUE]
  /\ UNCHANGED queue

UpreadEnqueue(t) ==
  /\ pc[t] = "Idle"
  /\ ~(IsEmpty(queue) /\ CanUpread(lock))
  /\ pc' = [pc EXCEPT ![t] = "WaitingUpread"]
  /\ queue' = Enqueue(queue, t, "Upread")
  /\ UNCHANGED lock

Upread(t) == UpreadImmediate(t) \/ UpreadEnqueue(t)

AcquireFromQueueRead(t) ==
  /\ pc[t] = "WaitingRead"
  /\ Len(queue) >= 1
  /\ queue[1].t = t
  /\ queue[1].kind = "Read"
  /\ queue[1].awake = TRUE
  /\ CanRead(lock)
  /\ pc' = [pc EXCEPT ![t] = "HoldingRead"]
  /\ lock' = [lock EXCEPT !.readers = lock.readers + 1]
  /\ queue' = Tail(queue)

AcquireFromQueueWrite(t) ==
  /\ pc[t] = "WaitingWrite"
  /\ Len(queue) >= 1
  /\ queue[1].t = t
  /\ queue[1].kind = "Write"
  /\ queue[1].awake = TRUE
  /\ CanWrite(lock)
  /\ pc' = [pc EXCEPT ![t] = "HoldingWrite"]
  /\ lock' = [lock EXCEPT !.writer = TRUE]
  /\ queue' = Tail(queue)

AcquireFromQueueUpread(t) ==
  /\ pc[t] = "WaitingUpread"
  /\ Len(queue) >= 1
  /\ queue[1].t = t
  /\ queue[1].kind = "Upread"
  /\ queue[1].awake = TRUE
  /\ CanUpread(lock)
  /\ pc' = [pc EXCEPT ![t] = "HoldingUpread"]
  /\ lock' = [lock EXCEPT !.upread = TRUE]
  /\ queue' = Tail(queue)

ReleaseRead(t) ==
  /\ pc[t] = "HoldingRead"
  /\ LET newReaders == lock.readers - 1 IN
     /\ pc' = [pc EXCEPT ![t] = "Idle"]
     /\ lock' = [lock EXCEPT !.readers = newReaders]
     /\ queue' = IF newReaders = 0 THEN WakeOne(queue) ELSE queue

ReleaseWrite(t) ==
  /\ pc[t] = "HoldingWrite"
  /\ pc' = [pc EXCEPT ![t] = "Idle"]
  /\ lock' = [lock EXCEPT !.writer = FALSE]
  /\ queue' = WakeAll(queue)

ReleaseUpread(t) ==
  /\ pc[t] = "HoldingUpread"
  /\ LET mustWake == (~lock.writer) /\ (lock.readers = 0) /\ (~lock.upgrading) IN
     /\ pc' = [pc EXCEPT ![t] = "Idle"]
     /\ lock' = [lock EXCEPT !.upread = FALSE]
     /\ queue' = IF mustWake THEN WakeAll(queue) ELSE queue

BeginUpgrade(t) ==
  /\ pc[t] = "HoldingUpread"
  /\ ~lock.upgrading
  /\ lock.upread
  /\ pc' = [pc EXCEPT ![t] = "Upgrading"]
  /\ lock' = [lock EXCEPT !.upgrading = TRUE]
  /\ UNCHANGED queue

FinishUpgrade(t) ==
  /\ pc[t] = "Upgrading"
  /\ lock.readers = 0
  /\ ~lock.writer
  /\ pc' = [pc EXCEPT ![t] = "HoldingWrite"]
  /\ lock' = [lock EXCEPT !.writer = TRUE, !.upgrading = FALSE, !.upread = FALSE]
  /\ UNCHANGED queue

Downgrade(t) ==
  /\ pc[t] = "HoldingWrite"
  /\ ~lock.upread
  /\ pc' = [pc EXCEPT ![t] = "HoldingUpread"]
  /\ lock' = [lock EXCEPT !.writer = FALSE, !.upread = TRUE]
  /\ UNCHANGED queue

Next ==
  \E t \in THREAD:
    \/ Read(t)
    \/ Write(t)
    \/ Upread(t)
    \/ AcquireFromQueueRead(t)
    \/ AcquireFromQueueWrite(t)
    \/ AcquireFromQueueUpread(t)
    \/ ReleaseRead(t)
    \/ ReleaseWrite(t)
    \/ ReleaseUpread(t)
    \/ BeginUpgrade(t)
    \/ FinishUpgrade(t)
    \/ Downgrade(t)

Spec ==
  Init /\ [][Next]_vars /\
  (\A t \in THREAD:
    WF_vars(AcquireFromQueueRead(t)) /\
    WF_vars(AcquireFromQueueWrite(t)) /\
    WF_vars(AcquireFromQueueUpread(t)) /\
    WF_vars(FinishUpgrade(t)))

====