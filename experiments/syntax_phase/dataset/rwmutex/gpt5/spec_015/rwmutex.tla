---- MODULE rwmutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANT THREADS

Mode == {"Idle", "Waiting", "Reading", "Writing", "Upread", "Upgrading"}
Op == {"Read", "Write", "Upread"}

LockType == [w : {0,1}, u : {0,1}, b : {0,1}, r : Nat]

Head(s) == s[1]
Tail(s) == IF Len(s) = 0 THEN << >> ELSE SubSeq(s, 2, Len(s))
SeqElems(s) == { s[i] : i \in 1..Len(s) }
InSeq(s,x) == \E i \in 1..Len(s) : s[i] = x

CanRead(l) == l.w = 0 /\ l.b = 0
CanWrite(l) == l.w = 0 /\ l.u = 0 /\ l.r = 0
CanUpread(l) == l.w = 0 /\ l.u = 0
ReadyToUpgrade(l) == l.r = 0 /\ l.w = 0 /\ l.u = 1 /\ l.b = 1

VARIABLES lock, Q, Woken, mode, req

TypeOK ==
  /\ lock \in LockType
  /\ Q \in Seq(THREADS)
  /\ Woken \subseteq SeqElems(Q)
  /\ mode \in [THREADS -> Mode]
  /\ req \in [THREADS -> Op]

Init ==
  /\ lock = [w |-> 0, u |-> 0, b |-> 0, r |-> 0]
  /\ Q = << >>
  /\ Woken = {}
  /\ mode = [t \in THREADS |-> "Idle"]
  /\ req = [t \in THREADS |-> "Read"]
  /\ TypeOK

TryReadAcquire(t) ==
  /\ t \in THREADS
  /\ mode[t] = "Idle"
  /\ Len(Q) = 0
  /\ CanRead(lock)
  /\ lock' = [lock EXCEPT !.r = @ + 1]
  /\ mode' = [mode EXCEPT ![t] = "Reading"]
  /\ UNCHANGED << Q, Woken, req >>

BlockRead(t) ==
  /\ t \in THREADS
  /\ mode[t] = "Idle"
  /\ (Len(Q) > 0 \/ ~CanRead(lock))
  /\ ~InSeq(Q, t)
  /\ Q' = Append(Q, t)
  /\ mode' = [mode EXCEPT ![t] = "Waiting"]
  /\ req' = [req EXCEPT ![t] = "Read"]
  /\ UNCHANGED << lock, Woken >>

DequeueReadAcquire(t) ==
  /\ t \in THREADS
  /\ mode[t] = "Waiting"
  /\ req[t] = "Read"
  /\ Len(Q) > 0
  /\ Head(Q) = t
  /\ t \in Woken
  /\ CanRead(lock)
  /\ lock' = [lock EXCEPT !.r = @ + 1]
  /\ Q' = Tail(Q)
  /\ mode' = [mode EXCEPT ![t] = "Reading"]
  /\ Woken' = Woken \ {t}
  /\ UNCHANGED req

TryWriteAcquire(t) ==
  /\ t \in THREADS
  /\ mode[t] = "Idle"
  /\ Len(Q) = 0
  /\ CanWrite(lock)
  /\ lock' = [lock EXCEPT !.w = 1]
  /\ mode' = [mode EXCEPT ![t] = "Writing"]
  /\ UNCHANGED << Q, Woken, req >>

BlockWrite(t) ==
  /\ t \in THREADS
  /\ mode[t] = "Idle"
  /\ (Len(Q) > 0 \/ ~CanWrite(lock))
  /\ ~InSeq(Q, t)
  /\ Q' = Append(Q, t)
  /\ mode' = [mode EXCEPT ![t] = "Waiting"]
  /\ req' = [req EXCEPT ![t] = "Write"]
  /\ UNCHANGED << lock, Woken >>

DequeueWriteAcquire(t) ==
  /\ t \in THREADS
  /\ mode[t] = "Waiting"
  /\ req[t] = "Write"
  /\ Len(Q) > 0
  /\ Head(Q) = t
  /\ t \in Woken
  /\ CanWrite(lock)
  /\ lock' = [lock EXCEPT !.w = 1]
  /\ Q' = Tail(Q)
  /\ mode' = [mode EXCEPT ![t] = "Writing"]
  /\ Woken' = Woken \ {t}
  /\ UNCHANGED req

TryUpreadAcquire(t) ==
  /\ t \in THREADS
  /\ mode[t] = "Idle"
  /\ Len(Q) = 0
  /\ CanUpread(lock)
  /\ lock' = [lock EXCEPT !.u = 1]
  /\ mode' = [mode EXCEPT ![t] = "Upread"]
  /\ UNCHANGED << Q, Woken, req >>

BlockUpread(t) ==
  /\ t \in THREADS
  /\ mode[t] = "Idle"
  /\ (Len(Q) > 0 \/ ~CanUpread(lock))
  /\ ~InSeq(Q, t)
  /\ Q' = Append(Q, t)
  /\ mode' = [mode EXCEPT ![t] = "Waiting"]
  /\ req' = [req EXCEPT ![t] = "Upread"]
  /\ UNCHANGED << lock, Woken >>

DequeueUpreadAcquire(t) ==
  /\ t \in THREADS
  /\ mode[t] = "Waiting"
  /\ req[t] = "Upread"
  /\ Len(Q) > 0
  /\ Head(Q) = t
  /\ t \in Woken
  /\ CanUpread(lock)
  /\ lock' = [lock EXCEPT !.u = 1]
  /\ Q' = Tail(Q)
  /\ mode' = [mode EXCEPT ![t] = "Upread"]
  /\ Woken' = Woken \ {t}
  /\ UNCHANGED req

ReaderRelease(t) ==
  /\ t \in THREADS
  /\ mode[t] = "Reading"
  /\ lock.r \geq 1
  /\ lock' = [lock EXCEPT !.r = @ - 1]
  /\ mode' = [mode EXCEPT ![t] = "Idle"]
  /\ Woken' =
       IF lock.r = 1 THEN
         IF Len(Q) = 0 THEN {}
         ELSE (Woken \cap SeqElems(Q)) \cup {Head(Q)}
       ELSE (Woken \cap SeqElems(Q))
  /\ UNCHANGED << Q, req >>

WriterRelease(t) ==
  /\ t \in THREADS
  /\ mode[t] = "Writing"
  /\ lock.w = 1
  /\ lock' = [lock EXCEPT !.w = 0]
  /\ mode' = [mode EXCEPT ![t] = "Idle"]
  /\ Woken' = SeqElems(Q)
  /\ UNCHANGED << Q, req >>

UpreadRelease(t) ==
  /\ t \in THREADS
  /\ mode[t] = "Upread"
  /\ lock.u = 1
  /\ lock.b = 0
  /\ lock' = [lock EXCEPT !.u = 0]
  /\ mode' = [mode EXCEPT ![t] = "Idle"]
  /\ Woken' = SeqElems(Q)
  /\ UNCHANGED << Q, req >>

StartUpgrade(t) ==
  /\ t \in THREADS
  /\ mode[t] = "Upread"
  /\ lock.b = 0
  /\ lock' = [lock EXCEPT !.b = 1]
  /\ mode' = [mode EXCEPT ![t] = "Upgrading"]
  /\ UNCHANGED << Q, Woken, req >>

TryUpgrade(t) ==
  /\ t \in THREADS
  /\ mode[t] = "Upgrading"
  /\ ReadyToUpgrade(lock)
  /\ lock' = [lock EXCEPT !.w = 1, !.u = 0, !.b = 0]
  /\ mode' = [mode EXCEPT ![t] = "Writing"]
  /\ UNCHANGED << Q, Woken, req >>

Downgrade(t) ==
  /\ t \in THREADS
  /\ mode[t] = "Writing"
  /\ lock.w = 1
  /\ lock.u = 0
  /\ lock' = [lock EXCEPT !.w = 0, !.u = 1]
  /\ mode' = [mode EXCEPT ![t] = "Upread"]
  /\ UNCHANGED << Q, Woken, req >>

ReadStep(t) == TryReadAcquire(t) \/ DequeueReadAcquire(t)
WriteStep(t) == TryWriteAcquire(t) \/ DequeueWriteAcquire(t)
UpreadStep(t) == TryUpreadAcquire(t) \/ DequeueUpreadAcquire(t)

Next ==
  \/ \E t \in THREADS : ReadStep(t) \/ BlockRead(t)
  \/ \E t \in THREADS : WriteStep(t) \/ BlockWrite(t)
  \/ \E t \in THREADS : UpreadStep(t) \/ BlockUpread(t)
  \/ \E t \in THREADS : ReaderRelease(t) \/ WriterRelease(t) \/ UpreadRelease(t)
  \/ \E t \in THREADS : StartUpgrade(t) \/ TryUpgrade(t) \/ Downgrade(t)

Vars == << lock, Q, Woken, mode, req >>

Spec ==
  Init /\ [][Next]_Vars
  /\ \A t \in THREADS : WF_Vars(ReadStep(t))
  /\ \A t \in THREADS : WF_Vars(WriteStep(t))
  /\ \A t \in THREADS : WF_Vars(UpreadStep(t))
  /\ \A t \in THREADS : WF_Vars(TryUpgrade(t))

====