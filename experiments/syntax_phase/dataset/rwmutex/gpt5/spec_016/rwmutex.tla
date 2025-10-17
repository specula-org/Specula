---- MODULE rwmutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANT THREAD

KIND == {"read", "write", "upread"}

MODES == {
    "idle",
    "waitingRead", "readyRead", "reading",
    "waitingWrite", "readyWrite", "writing",
    "waitingUpread", "readyUpread", "upreading", "upgrading"
}

VARIABLES lock, mode, Q

TypeOK ==
    /\ lock \in [writer: {0,1}, up: {0,1}, being: {0,1}, readers: Nat]
    /\ mode \in [THREAD -> MODES]
    /\ Q \in Seq([t: THREAD, kind: KIND])

Init ==
    /\ lock = [writer |-> 0, up |-> 0, being |-> 0, readers |-> 0]
    /\ mode = [t \in THREAD |-> "idle"]
    /\ Q = <<>>

InQ(t) == \E i \in 1..Len(Q): Q[i].t = t

CanRead == lock.writer = 0 /\ lock.being = 0
CanWrite == lock.writer = 0 /\ lock.up = 0 /\ lock.readers = 0
CanUpread == lock.writer = 0 /\ lock.up = 0
CanUpgrade == lock.writer = 0 /\ lock.readers = 0 /\ lock.up = 1 /\ lock.being = 1

ReadyMode(k) ==
    IF k = "read" THEN "readyRead"
    ELSE IF k = "write" THEN "readyWrite"
    ELSE "readyUpread"

StartReadAcquire(t) ==
    /\ mode[t] = "idle"
    /\ CanRead
    /\ lock' = [lock EXCEPT !.readers = @ + 1]
    /\ mode' = [mode EXCEPT ![t] = "reading"]
    /\ Q' = Q

StartReadEnqueue(t) ==
    /\ mode[t] = "idle"
    /\ ~CanRead
    /\ ~InQ(t)
    /\ Q' = Append(Q, [t |-> t, kind |-> "read"])
    /\ mode' = [mode EXCEPT ![t] = "waitingRead"]
    /\ lock' = lock

StartWriteAcquire(t) ==
    /\ mode[t] = "idle"
    /\ CanWrite
    /\ lock' = [lock EXCEPT !.writer = 1]
    /\ mode' = [mode EXCEPT ![t] = "writing"]
    /\ Q' = Q

StartWriteEnqueue(t) ==
    /\ mode[t] = "idle"
    /\ ~CanWrite
    /\ ~InQ(t)
    /\ Q' = Append(Q, [t |-> t, kind |-> "write"])
    /\ mode' = [mode EXCEPT ![t] = "waitingWrite"]
    /\ lock' = lock

StartUpreadAcquire(t) ==
    /\ mode[t] = "idle"
    /\ CanUpread
    /\ lock' = [lock EXCEPT !.up = 1]
    /\ mode' = [mode EXCEPT ![t] = "upreading"]
    /\ Q' = Q

StartUpreadEnqueue(t) ==
    /\ mode[t] = "idle"
    /\ ~CanUpread
    /\ ~InQ(t)
    /\ Q' = Append(Q, [t |-> t, kind |-> "upread"])
    /\ mode' = [mode EXCEPT ![t] = "waitingUpread"]
    /\ lock' = lock

RReadyTrySucc(t) ==
    /\ mode[t] = "readyRead"
    /\ CanRead
    /\ lock' = [lock EXCEPT !.readers = @ + 1]
    /\ mode' = [mode EXCEPT ![t] = "reading"]
    /\ Q' = Q

RReadyTryFail(t) ==
    /\ mode[t] = "readyRead"
    /\ ~CanRead
    /\ Q' = Append(Q, [t |-> t, kind |-> "read"])
    /\ mode' = [mode EXCEPT ![t] = "waitingRead"]
    /\ lock' = lock

WReadyTrySucc(t) ==
    /\ mode[t] = "readyWrite"
    /\ CanWrite
    /\ lock' = [lock EXCEPT !.writer = 1]
    /\ mode' = [mode EXCEPT ![t] = "writing"]
    /\ Q' = Q

WReadyTryFail(t) ==
    /\ mode[t] = "readyWrite"
    /\ ~CanWrite
    /\ Q' = Append(Q, [t |-> t, kind |-> "write"])
    /\ mode' = [mode EXCEPT ![t] = "waitingWrite"]
    /\ lock' = lock

UReadyTrySucc(t) ==
    /\ mode[t] = "readyUpread"
    /\ CanUpread
    /\ lock' = [lock EXCEPT !.up = 1]
    /\ mode' = [mode EXCEPT ![t] = "upreading"]
    /\ Q' = Q

UReadyTryFail(t) ==
    /\ mode[t] = "readyUpread"
    /\ ~CanUpread
    /\ Q' = Append(Q, [t |-> t, kind |-> "upread"])
    /\ mode' = [mode EXCEPT ![t] = "waitingUpread"]
    /\ lock' = lock

ReleaseRead(t) ==
    /\ mode[t] = "reading"
    /\ LET newReaders == lock.readers - 1 IN
       /\ lock' = [lock EXCEPT !.readers = newReaders]
       /\ IF newReaders = 0 /\ Len(Q) > 0 THEN
             LET e == Q[1] IN
             /\ Q' = SubSeq(Q, 2, Len(Q))
             /\ mode' = [mode EXCEPT
                          ![t] = "idle",
                          ![e.t] = ReadyMode(e.kind)]
          ELSE
             /\ Q' = Q
             /\ mode' = [mode EXCEPT ![t] = "idle"]

ReleaseWrite(t) ==
    /\ mode[t] = "writing"
    /\ lock' = [lock EXCEPT !.writer = 0]
    /\ Q' = <<>>
    /\ mode' = [u \in THREAD |-> 
                  IF u = t THEN "idle"
                  ELSE IF mode[u] = "waitingRead" THEN "readyRead"
                  ELSE IF mode[u] = "waitingWrite" THEN "readyWrite"
                  ELSE IF mode[u] = "waitingUpread" THEN "readyUpread"
                  ELSE mode[u]]

ReleaseUpread(t) ==
    /\ mode[t] = "upreading"
    /\ LET onlyUp == (lock.up = 1 /\ lock.writer = 0 /\ lock.readers = 0 /\ lock.being = 0) IN
       /\ lock' = [lock EXCEPT !.up = 0]
       /\ IF onlyUp THEN
             /\ Q' = <<>>
             /\ mode' = [u \in THREAD |->
                           IF u = t THEN "idle"
                           ELSE IF mode[u] = "waitingRead" THEN "readyRead"
                           ELSE IF mode[u] = "waitingWrite" THEN "readyWrite"
                           ELSE IF mode[u] = "waitingUpread" THEN "readyUpread"
                           ELSE mode[u]]
          ELSE
             /\ Q' = Q
             /\ mode' = [mode EXCEPT ![t] = "idle"]

UpgradeStart(t) ==
    /\ mode[t] = "upreading"
    /\ lock.up = 1
    /\ lock' = [lock EXCEPT !.being = 1]
    /\ mode' = [mode EXCEPT ![t] = "upgrading"]
    /\ Q' = Q

UpgradeSuccess(t) ==
    /\ mode[t] = "upgrading"
    /\ CanUpgrade
    /\ lock' = [lock EXCEPT !.writer = 1, !.up = 0, !.being = 0]
    /\ mode' = [mode EXCEPT ![t] = "writing"]
    /\ Q' = Q

Downgrade(t) ==
    /\ mode[t] = "writing"
    /\ lock' = [lock EXCEPT !.writer = 0, !.up = 1]
    /\ Q' = <<>>
    /\ mode' = [u \in THREAD |-> 
                  IF u = t THEN "upreading"
                  ELSE IF mode[u] = "waitingRead" THEN "readyRead"
                  ELSE IF mode[u] = "waitingWrite" THEN "readyWrite"
                  ELSE IF mode[u] = "waitingUpread" THEN "readyUpread"
                  ELSE mode[u]]

Next ==
    \E t \in THREAD:
        StartReadAcquire(t) \/ StartReadEnqueue(t)
      \/ StartWriteAcquire(t) \/ StartWriteEnqueue(t)
      \/ StartUpreadAcquire(t) \/ StartUpreadEnqueue(t)
      \/ RReadyTrySucc(t) \/ RReadyTryFail(t)
      \/ WReadyTrySucc(t) \/ WReadyTryFail(t)
      \/ UReadyTrySucc(t) \/ UReadyTryFail(t)
      \/ ReleaseRead(t) \/ ReleaseWrite(t) \/ ReleaseUpread(t)
      \/ UpgradeStart(t) \/ UpgradeSuccess(t) \/ Downgrade(t)

vars == << lock, mode, Q >>

Spec ==
    Init /\ [][Next]_vars
    /\ \A t \in THREAD: WF_vars(RReadyTrySucc(t))
    /\ \A t \in THREAD: WF_vars(WReadyTrySucc(t))
    /\ \A t \in THREAD: WF_vars(UReadyTrySucc(t))
    /\ \A t \in THREAD: WF_vars(UpgradeSuccess(t))

====