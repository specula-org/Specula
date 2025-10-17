---- MODULE rwmutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANT THREADS

Ops == {"Read", "Write", "Upread"}

WaitElemSet == [t: THREADS, op: Ops]

VARIABLES lock, Q, allowed, State

TypeOK ==
    /\ lock \in [writer: BOOLEAN, upread: BOOLEAN, upgrading: BOOLEAN, readers: Nat]
    /\ Q \in Seq(WaitElemSet)
    /\ allowed \subseteq THREADS
    /\ State \in [THREADS -> {"Idle", "Read", "Write", "Upread"}]

Init ==
    /\ lock = [writer |-> FALSE, upread |-> FALSE, upgrading |-> FALSE, readers |-> 0]
    /\ Q = << >>
    /\ allowed = {}
    /\ State = [t \in THREADS |-> "Idle"]

Indices == 1..Len(Q)

Waiting(t) == \E i \in Indices: Q[i].t = t

WaitingTids(Q_) == { Q_[i].t : i \in 1..Len(Q_) }

RemoveAt(s, i) == SubSeq(s, 1, i-1) \o SubSeq(s, i+1, Len(s))

CanRead(l) == ~l.writer /\ ~l.upgrading
CanWrite(l) == ~l.writer /\ ~l.upread /\ l.readers = 0
CanUpread(l) == ~l.writer /\ ~l.upread

ReadImmediate(t) ==
    /\ State[t] = "Idle"
    /\ ~Waiting(t)
    /\ CanRead(lock)
    /\ State' = [State EXCEPT ![t] = "Read"]
    /\ lock' = [lock EXCEPT !.readers = @ + 1]
    /\ UNCHANGED <<Q, allowed>>

ReadEnqueue(t) ==
    /\ State[t] = "Idle"
    /\ ~Waiting(t)
    /\ ~CanRead(lock)
    /\ Q' = Append(Q, [t |-> t, op |-> "Read"])
    /\ allowed' = allowed \ {t}
    /\ UNCHANGED <<lock, State>>

ReadFromWait(t) ==
    /\ State[t] = "Idle"
    /\ Waiting(t)
    /\ t \in allowed
    /\ CanRead(lock)
    /\ LET i == CHOOSE k \in Indices: Q[k].t = t
       IN /\ \A j \in 1..i: Q[j].op = "Read" /\ Q[j].t \in allowed
          /\ Q' = RemoveAt(Q, i)
          /\ allowed' = allowed \ {t}
          /\ State' = [State EXCEPT ![t] = "Read"]
          /\ lock' = [lock EXCEPT !.readers = @ + 1]

WriteImmediate(t) ==
    /\ State[t] = "Idle"
    /\ ~Waiting(t)
    /\ CanWrite(lock)
    /\ State' = [State EXCEPT ![t] = "Write"]
    /\ lock' = [lock EXCEPT !.writer = TRUE]
    /\ UNCHANGED <<Q, allowed>>

WriteEnqueue(t) ==
    /\ State[t] = "Idle"
    /\ ~Waiting(t)
    /\ ~CanWrite(lock)
    /\ Q' = Append(Q, [t |-> t, op |-> "Write"])
    /\ allowed' = allowed \ {t}
    /\ UNCHANGED <<lock, State>>

WriteFromWait(t) ==
    /\ State[t] = "Idle"
    /\ Waiting(t)
    /\ t \in allowed
    /\ CanWrite(lock)
    /\ Len(Q) >= 1 /\ Q[1].t = t
    /\ Q' = RemoveAt(Q, 1)
    /\ allowed' = allowed \ {t}
    /\ State' = [State EXCEPT ![t] = "Write"]
    /\ lock' = [lock EXCEPT !.writer = TRUE]

UpreadImmediate(t) ==
    /\ State[t] = "Idle"
    /\ ~Waiting(t)
    /\ CanUpread(lock)
    /\ State' = [State EXCEPT ![t] = "Upread"]
    /\ lock' = [lock EXCEPT !.upread = TRUE]
    /\ UNCHANGED <<Q, allowed>>

UpreadEnqueue(t) ==
    /\ State[t] = "Idle"
    /\ ~Waiting(t)
    /\ ~CanUpread(lock)
    /\ Q' = Append(Q, [t |-> t, op |-> "Upread"])
    /\ allowed' = allowed \ {t}
    /\ UNCHANGED <<lock, State>>

UpreadFromWait(t) ==
    /\ State[t] = "Idle"
    /\ Waiting(t)
    /\ t \in allowed
    /\ CanUpread(lock)
    /\ Len(Q) >= 1 /\ Q[1].t = t
    /\ Q' = RemoveAt(Q, 1)
    /\ allowed' = allowed \ {t}
    /\ State' = [State EXCEPT ![t] = "Upread"]
    /\ lock' = [lock EXCEPT !.upread = TRUE]

ReadRelease(t) ==
    /\ State[t] = "Read"
    /\ lock.readers >= 1
    /\ LET newReaders == lock.readers - 1 IN
       /\ lock' = [lock EXCEPT !.readers = newReaders]
       /\ allowed' =
            IF newReaders = 0 /\ Len(Q) >= 1
            THEN allowed \cup {Q[1].t}
            ELSE allowed
       /\ State' = [State EXCEPT ![t] = "Idle"]
       /\ UNCHANGED Q

WriteRelease(t) ==
    /\ State[t] = "Write"
    /\ lock.writer
    /\ lock' = [lock EXCEPT !.writer = FALSE]
    /\ allowed' = allowed \cup WaitingTids(Q)
    /\ State' = [State EXCEPT ![t] = "Idle"]
    /\ UNCHANGED Q

UpreadRelease(t) ==
    /\ State[t] = "Upread"
    /\ lock.upread
    /\ State' = [State EXCEPT ![t] = "Idle"]
    /\ lock' = [lock EXCEPT !.upread = FALSE]
    /\ allowed' =
         IF ~lock.writer /\ lock.readers = 0 /\ ~lock.upgrading
         THEN allowed \cup WaitingTids(Q)
         ELSE allowed
    /\ UNCHANGED Q

BeginUpgrade(t) ==
    /\ State[t] = "Upread"
    /\ lock.upread
    /\ ~lock.upgrading
    /\ lock' = [lock EXCEPT !.upgrading = TRUE]
    /\ UNCHANGED <<Q, allowed, State>>

FinishUpgrade(t) ==
    /\ State[t] = "Upread"
    /\ lock.upread
    /\ lock.upgrading
    /\ lock.readers = 0
    /\ State' = [State EXCEPT ![t] = "Write"]
    /\ lock' = [lock EXCEPT !.writer = TRUE, !.upread = FALSE, !.upgrading = FALSE]
    /\ UNCHANGED <<Q, allowed>>

Downgrade(t) ==
    /\ State[t] = "Write"
    /\ lock.writer
    /\ State' = [State EXCEPT ![t] = "Upread"]
    /\ lock' = [lock EXCEPT !.writer = FALSE, !.upread = TRUE]
    /\ UNCHANGED <<Q, allowed>>

Next ==
    \E t \in THREADS:
        \/ ReadImmediate(t)
        \/ ReadEnqueue(t)
        \/ ReadFromWait(t)
        \/ WriteImmediate(t)
        \/ WriteEnqueue(t)
        \/ WriteFromWait(t)
        \/ UpreadImmediate(t)
        \/ UpreadEnqueue(t)
        \/ UpreadFromWait(t)
        \/ ReadRelease(t)
        \/ WriteRelease(t)
        \/ UpreadRelease(t)
        \/ BeginUpgrade(t)
        \/ FinishUpgrade(t)
        \/ Downgrade(t)

Vars == <<lock, Q, allowed, State>>

Spec ==
    Init
    /\ [][Next]_Vars
    /\ \A t \in THREADS:
         /\ WF_Vars(ReadFromWait(t))
         /\ WF_Vars(WriteFromWait(t))
         /\ WF_Vars(UpreadFromWait(t))
         /\ WF_Vars(FinishUpgrade(t))

====