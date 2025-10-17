---- MODULE rwmutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Threads

VARIABLES holds, lock, queue

Mode == {"N","R","W","U"}

Append(s, e) == s \o << e >>

Drop(s, n) ==
  IF n = 0 THEN s
  ELSE IF n >= Len(s) THEN << >>
  ELSE SubSeq(s, n+1, Len(s))

Readers(S) == { t \in Threads : S[t] = "R" }
UpHolders(S) == { t \in Threads : S[t] = "U" }
Writers(S) == { t \in Threads : S[t] = "W" }

NotInQueue(t) == \A i \in 1..Len(queue) : queue[i].th # t

TypeOK ==
  holds \in [Threads -> Mode] /\
  lock \in [w : {0,1}, u : {0,1}, b : {0,1}, r : Nat] /\
  queue \in Seq([th : Threads, kind : {"R","W","U"}, sleep : BOOLEAN]) /\
  lock.r = Cardinality(Readers(holds)) /\
  lock.u = IF Cardinality(UpHolders(holds)) > 0 THEN 1 ELSE 0 /\
  lock.w = IF Cardinality(Writers(holds)) > 0 THEN 1 ELSE 0

Init ==
  holds = [t \in Threads |-> "N"] /\
  lock = [w |-> 0, u |-> 0, b |-> 0, r |-> 0] /\
  queue = << >> /\
  TypeOK

ReadAcquireDirect(t) ==
  /\ t \in Threads
  /\ holds[t] = "N"
  /\ NotInQueue(t)
  /\ queue = << >>
  /\ lock.w = 0 /\ lock.b = 0
  /\ holds' = [holds EXCEPT ![t] = "R"]
  /\ lock' = [lock EXCEPT !.r = @ + 1]
  /\ queue' = queue

EnqueueRead(t) ==
  /\ t \in Threads
  /\ holds[t] = "N"
  /\ NotInQueue(t)
  /\ ~ (queue = << >> /\ lock.w = 0 /\ lock.b = 0)
  /\ queue' = Append(queue, [th |-> t, kind |-> "R", sleep |-> TRUE])
  /\ holds' = holds
  /\ lock' = lock

GrantFrontReaders ==
  LET AwakeR(i) == i \in 1..Len(queue) /\ queue[i].kind = "R" /\ queue[i].sleep = FALSE IN
  /\ queue # << >>
  /\ \E k \in 1..Len(queue) :
       /\ (\A i \in 1..k : AwakeR(i))
       /\ (k = Len(queue) \/ ~AwakeR(k+1))
       /\ lock.w = 0 /\ lock.b = 0
       /\ LET TS == { queue[i].th : i \in 1..k } IN
            /\ holds' = [x \in Threads |-> IF x \in TS THEN "R" ELSE holds[x]]
            /\ lock' = [lock EXCEPT !.r = @ + k]
            /\ queue' = Drop(queue, k)

ReadRelease(t) ==
  /\ t \in Threads
  /\ holds[t] = "R"
  /\ holds' = [holds EXCEPT ![t] = "N"]
  /\ lock'.r = lock.r - 1
  /\ lock'.w = lock.w
  /\ lock'.u = lock.u
  /\ lock'.b = lock.b
  /\ IF lock.r = 1 /\ \E i \in 1..Len(queue) : queue[i].sleep
     THEN
       /\ \E i \in 1..Len(queue) :
           /\ queue[i].sleep
           /\ \A j \in 1..(i-1) : ~queue[j].sleep
           /\ queue' = [queue EXCEPT ![i].sleep = FALSE]
     ELSE /\ queue' = queue

WriteAcquireDirect(t) ==
  /\ t \in Threads
  /\ holds[t] = "N"
  /\ NotInQueue(t)
  /\ queue = << >>
  /\ lock.r = 0 /\ lock.w = 0 /\ lock.u = 0 /\ lock.b = 0
  /\ holds' = [holds EXCEPT ![t] = "W"]
  /\ lock' = [lock EXCEPT !.w = 1]
  /\ queue' = queue

EnqueueWrite(t) ==
  /\ t \in Threads
  /\ holds[t] = "N"
  /\ NotInQueue(t)
  /\ ~ (queue = << >> /\ lock.r = 0 /\ lock.w = 0 /\ lock.u = 0 /\ lock.b = 0)
  /\ queue' = Append(queue, [th |-> t, kind |-> "W", sleep |-> TRUE])
  /\ holds' = holds
  /\ lock' = lock

GrantFrontWriter ==
  /\ queue # << >>
  /\ queue[1].kind = "W"
  /\ queue[1].sleep = FALSE
  /\ lock.r = 0 /\ lock.w = 0 /\ lock.u = 0 /\ lock.b = 0
  /\ LET t == queue[1].th IN
       /\ holds' = [holds EXCEPT ![t] = "W"]
       /\ lock' = [lock EXCEPT !.w = 1]
       /\ queue' = SubSeq(queue, 2, Len(queue))

WriteRelease(t) ==
  /\ t \in Threads
  /\ holds[t] = "W"
  /\ holds' = [holds EXCEPT ![t] = "N"]
  /\ lock' = [lock EXCEPT !.w = 0]
  /\ queue' = [ i \in 1..Len(queue) |-> [queue[i] EXCEPT !.sleep = FALSE] ]

Downgrade(t) ==
  /\ t \in Threads
  /\ holds[t] = "W"
  /\ holds' = [holds EXCEPT ![t] = "U"]
  /\ lock' = [lock EXCEPT !.w = 0, !.u = 1]
  /\ queue' = queue

UpreadAcquireDirect(t) ==
  /\ t \in Threads
  /\ holds[t] = "N"
  /\ NotInQueue(t)
  /\ queue = << >>
  /\ lock.w = 0 /\ lock.u = 0
  /\ holds' = [holds EXCEPT ![t] = "U"]
  /\ lock' = [lock EXCEPT !.u = 1]
  /\ queue' = queue

EnqueueUpread(t) ==
  /\ t \in Threads
  /\ holds[t] = "N"
  /\ NotInQueue(t)
  /\ ~ (queue = << >> /\ lock.w = 0 /\ lock.u = 0)
  /\ queue' = Append(queue, [th |-> t, kind |-> "U", sleep |-> TRUE])
  /\ holds' = holds
  /\ lock' = lock

GrantFrontUpread ==
  /\ queue # << >>
  /\ queue[1].kind = "U"
  /\ queue[1].sleep = FALSE
  /\ lock.w = 0 /\ lock.u = 0
  /\ LET t == queue[1].th IN
       /\ holds' = [holds EXCEPT ![t] = "U"]
       /\ lock' = [lock EXCEPT !.u = 1]
       /\ queue' = SubSeq(queue, 2, Len(queue))

UpreadRelease(t) ==
  /\ t \in Threads
  /\ holds[t] = "U"
  /\ holds' = [holds EXCEPT ![t] = "N"]
  /\ IF lock.w = 0 /\ lock.r = 0 /\ lock.b = 0 /\ lock.u = 1
     THEN
       /\ lock' = [lock EXCEPT !.u = 0]
       /\ queue' = [ i \in 1..Len(queue) |-> [queue[i] EXCEPT !.sleep = FALSE] ]
     ELSE
       /\ lock' = [lock EXCEPT !.u = 0]
       /\ queue' = queue

BeginUpgrade(t) ==
  /\ t \in Threads
  /\ holds[t] = "U"
  /\ lock.b = 0
  /\ holds' = holds
  /\ lock' = [lock EXCEPT !.b = 1]
  /\ queue' = queue

TryUpgrade(t) ==
  /\ t \in Threads
  /\ holds[t] = "U"
  /\ lock.b = 1 /\ lock.w = 0 /\ lock.r = 0
  /\ holds' = [holds EXCEPT ![t] = "W"]
  /\ lock' = [lock EXCEPT !.w = 1, !.u = 0, !.b = 0]
  /\ queue' = queue

vars == << holds, lock, queue >>

Next ==
  \/ \E t \in Threads : ReadAcquireDirect(t)
  \/ \E t \in Threads : EnqueueRead(t)
  \/ GrantFrontReaders
  \/ \E t \in Threads : ReadRelease(t)
  \/ \E t \in Threads : WriteAcquireDirect(t)
  \/ \E t \in Threads : EnqueueWrite(t)
  \/ GrantFrontWriter
  \/ \E t \in Threads : WriteRelease(t)
  \/ \E t \in Threads : Downgrade(t)
  \/ \E t \in Threads : UpreadAcquireDirect(t)
  \/ \E t \in Threads : EnqueueUpread(t)
  \/ GrantFrontUpread
  \/ \E t \in Threads : UpreadRelease(t)
  \/ \E t \in Threads : BeginUpgrade(t)
  \/ \E t \in Threads : TryUpgrade(t)
  \/ UNCHANGED vars

Spec ==
  Init /\ [][Next]_vars /\
  WF_vars(GrantFrontReaders) /\
  WF_vars(GrantFrontWriter) /\
  WF_vars(GrantFrontUpread) /\
  WF_vars(TryUpgrade)

====