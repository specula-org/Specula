---- MODULE rwmutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS THREADS

OPS == {"R","W","U"}
STATES == {"Idle","WantR","WantW","WantU","R","W","U","Upgrading"}

WaitEntry(e) == /\ e \in [tid: THREADS, op: OPS]

CanRead(L) == /\ ~L.writer /\ ~L.upgrading
CanWrite(L) == /\ ~L.writer /\ ~L.upread /\ L.readers = 0
CanUpread(L) == /\ ~L.writer /\ ~L.upread

Waiters(Q) == { Q[i].tid : i \in 1..Len(Q) }

HeadIs(Q, op) == /\ Len(Q) # 0 /\ Q[1].op = op
HeadTid(Q) == Q[1].tid

IsReaderPrefixIndex(i, Q) == /\ i \in 1..Len(Q) /\ \A k \in 1..i: Q[k].op = "R"

Concat(s, t) ==
  [ i \in 1..(Len(s) + Len(t)) |->
      IF i <= Len(s) THEN s[i] ELSE t[i - Len(s)] ]

RemoveAt(Q, i) == Concat(SubSeq(Q, 1, i-1), SubSeq(Q, i+1, Len(Q)))

VARIABLES L, state, Q, Woken

TypeOK ==
  /\ L \in [writer: BOOLEAN, upread: BOOLEAN, upgrading: BOOLEAN, readers: Nat]
  /\ state \in [THREADS -> STATES]
  /\ Q \in Seq({ e \in [tid: THREADS, op: OPS] : TRUE })
  /\ Woken \subseteq THREADS

Init ==
  /\ L = [writer |-> FALSE, upread |-> FALSE, upgrading |-> FALSE, readers |-> 0]
  /\ state = [t \in THREADS |-> "Idle"]
  /\ Q = << >>
  /\ Woken = {}

ReadAcquireNow(t) ==
  /\ t \in THREADS
  /\ state[t] = "Idle"
  /\ CanRead(L)
  /\ L' = [L EXCEPT !.readers = @ + 1]
  /\ state' = [state EXCEPT ![t] = "R"]
  /\ Q' = Q
  /\ Woken' = Woken

ReadEnqueue(t) ==
  /\ t \in THREADS
  /\ state[t] = "Idle"
  /\ ~CanRead(L)
  /\ Q' = Append(Q, [tid |-> t, op |-> "R"])
  /\ state' = [state EXCEPT ![t] = "WantR"]
  /\ L' = L
  /\ Woken' = Woken

WriteAcquireNow(t) ==
  /\ t \in THREADS
  /\ state[t] = "Idle"
  /\ CanWrite(L)
  /\ L' = [L EXCEPT !.writer = TRUE]
  /\ state' = [state EXCEPT ![t] = "W"]
  /\ Q' = Q
  /\ Woken' = Woken

WriteEnqueue(t) ==
  /\ t \in THREADS
  /\ state[t] = "Idle"
  /\ ~CanWrite(L)
  /\ Q' = Append(Q, [tid |-> t, op |-> "W"])
  /\ state' = [state EXCEPT ![t] = "WantW"]
  /\ L' = L
  /\ Woken' = Woken

UpreadAcquireNow(t) ==
  /\ t \in THREADS
  /\ state[t] = "Idle"
  /\ CanUpread(L)
  /\ L' = [L EXCEPT !.upread = TRUE]
  /\ state' = [state EXCEPT ![t] = "U"]
  /\ Q' = Q
  /\ Woken' = Woken

UpreadEnqueue(t) ==
  /\ t \in THREADS
  /\ state[t] = "Idle"
  /\ ~CanUpread(L)
  /\ Q' = Append(Q, [tid |-> t, op |-> "U"])
  /\ state' = [state EXCEPT ![t] = "WantU"]
  /\ L' = L
  /\ Woken' = Woken

AcquireFromQueueR(t) ==
  \E i \in 1..Len(Q):
    /\ t \in THREADS
    /\ t \in Woken
    /\ Q[i].tid = t
    /\ IsReaderPrefixIndex(i, Q)
    /\ CanRead(L)
    /\ L' = [L EXCEPT !.readers = @ + 1]
    /\ state' = [state EXCEPT ![t] = "R"]
    /\ Q' = RemoveAt(Q, i)
    /\ Woken' = Woken \ {t}

AcquireFromQueueW(t) ==
  /\ t \in THREADS
  /\ Len(Q) # 0
  /\ HeadIs(Q, "W")
  /\ t = HeadTid(Q)
  /\ t \in Woken
  /\ CanWrite(L)
  /\ L' = [L EXCEPT !.writer = TRUE]
  /\ state' = [state EXCEPT ![t] = "W"]
  /\ Q' = SubSeq(Q, 2, Len(Q))
  /\ Woken' = Woken \ {t}

AcquireFromQueueU(t) ==
  /\ t \in THREADS
  /\ Len(Q) # 0
  /\ HeadIs(Q, "U")
  /\ t = HeadTid(Q)
  /\ t \in Woken
  /\ CanUpread(L)
  /\ L' = [L EXCEPT !.upread = TRUE]
  /\ state' = [state EXCEPT ![t] = "U"]
  /\ Q' = SubSeq(Q, 2, Len(Q))
  /\ Woken' = Woken \ {t}

ReadRelease(t) ==
  /\ t \in THREADS
  /\ state[t] = "R"
  /\ L.readers > 0
  /\ LET newReaders == L.readers - 1 IN
       /\ L' = [L EXCEPT !.readers = newReaders]
       /\ state' = [state EXCEPT ![t] = "Idle"]
       /\ Q' = Q
       /\ Woken' =
            IF newReaders = 0 /\ Len(Q) # 0
              THEN Woken \cup { HeadTid(Q) }
              ELSE Woken

WriteRelease(t) ==
  /\ t \in THREADS
  /\ state[t] = "W"
  /\ L.writer
  /\ L' = [L EXCEPT !.writer = FALSE]
  /\ state' = [state EXCEPT ![t] = "Idle"]
  /\ Q' = Q
  /\ Woken' = Woken \cup Waiters(Q)

UpreadRelease(t) ==
  /\ t \in THREADS
  /\ state[t] = "U"
  /\ L.upread
  /\ L' = [L EXCEPT !.upread = FALSE]
  /\ state' = [state EXCEPT ![t] = "Idle"]
  /\ Q' = Q
  /\ Woken' = Woken \cup Waiters(Q)

UpgradeBegin(t) ==
  /\ t \in THREADS
  /\ state[t] = "U"
  /\ ~L.upgrading
  /\ L' = [L EXCEPT !.upgrading = TRUE]
  /\ state' = [state EXCEPT ![t] = "Upgrading"]
  /\ Q' = Q
  /\ Woken' = Woken

UpgradeFinish(t) ==
  /\ t \in THREADS
  /\ state[t] = "Upgrading"
  /\ L.upgrading
  /\ L.readers = 0
  /\ L' = [L EXCEPT !.writer = TRUE, !.upread = FALSE, !.upgrading = FALSE]
  /\ state' = [state EXCEPT ![t] = "W"]
  /\ Q' = Q
  /\ Woken' = Woken

Downgrade(t) ==
  /\ t \in THREADS
  /\ state[t] = "W"
  /\ L.writer
  /\ L' = [L EXCEPT !.writer = FALSE, !.upread = TRUE]
  /\ state' = [state EXCEPT ![t] = "U"]
  /\ Q' = Q
  /\ Woken' = Woken

Next ==
  \E t \in THREADS:
    \/ ReadAcquireNow(t)
    \/ ReadEnqueue(t)
    \/ WriteAcquireNow(t)
    \/ WriteEnqueue(t)
    \/ UpreadAcquireNow(t)
    \/ UpreadEnqueue(t)
    \/ AcquireFromQueueR(t)
    \/ AcquireFromQueueW(t)
    \/ AcquireFromQueueU(t)
    \/ ReadRelease(t)
    \/ WriteRelease(t)
    \/ UpreadRelease(t)
    \/ UpgradeBegin(t)
    \/ UpgradeFinish(t)
    \/ Downgrade(t)

vars == << L, state, Q, Woken >>

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A t \in THREADS: WF_vars(AcquireFromQueueR(t))
  /\ \A t \in THREADS: WF_vars(AcquireFromQueueW(t))
  /\ \A t \in THREADS: WF_vars(AcquireFromQueueU(t))
  /\ \A t \in THREADS: WF_vars(UpgradeFinish(t))

====