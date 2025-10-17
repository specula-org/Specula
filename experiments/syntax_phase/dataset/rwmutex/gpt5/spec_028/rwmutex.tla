---- MODULE raftkvs ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Threads, None, Read, Write, Upread, Null

VARIABLES
  Lock,
  Q,
  Mode,
  WakeAll,
  Upgrading

vars == << Lock, Q, Mode, WakeAll, Upgrading >>

Kinds == {Read, Write, Upread}
Modes == {None} \cup Kinds

TidsInQ(s) == { s[i].tid : i \in 1..Len(s) }

Init ==
  /\ Lock = [ writer |-> FALSE, upread |-> FALSE, beingUpgraded |-> FALSE, readers |-> 0 ]
  /\ Q = << >>
  /\ Mode \in [Threads -> Modes]
  /\ \A t \in Threads: Mode[t] = None
  /\ WakeAll = FALSE
  /\ Upgrading = Null

RequestRead(t) ==
  /\ t \in Threads
  /\ Mode[t] = None
  /\ t \notin TidsInQ(Q)
  /\ IF Len(Q) = 0 /\ ~Lock.writer /\ ~Lock.beingUpgraded
     THEN
       /\ Lock' = [Lock EXCEPT !.readers = @ + 1]
       /\ Mode' = [Mode EXCEPT ![t] = Read]
       /\ UNCHANGED << Q, WakeAll, Upgrading >>
     ELSE
       /\ Q' = Append(Q, [tid |-> t, kind |-> Read])
       /\ UNCHANGED << Lock, Mode, WakeAll, Upgrading >>

RequestWrite(t) ==
  /\ t \in Threads
  /\ Mode[t] = None
  /\ t \notin TidsInQ(Q)
  /\ IF Len(Q) = 0 /\ ~Lock.writer /\ ~Lock.upread /\ Lock.readers = 0 /\ ~Lock.beingUpgraded
     THEN
       /\ Lock' = [Lock EXCEPT !.writer = TRUE]
       /\ Mode' = [Mode EXCEPT ![t] = Write]
       /\ UNCHANGED << Q, WakeAll, Upgrading >>
     ELSE
       /\ Q' = Append(Q, [tid |-> t, kind |-> Write])
       /\ UNCHANGED << Lock, Mode, WakeAll, Upgrading >>

RequestUpread(t) ==
  /\ t \in Threads
  /\ Mode[t] = None
  /\ t \notin TidsInQ(Q)
  /\ IF Len(Q) = 0 /\ ~Lock.writer /\ ~Lock.upread
     THEN
       /\ Lock' = [Lock EXCEPT !.upread = TRUE]
       /\ Mode' = [Mode EXCEPT ![t] = Upread]
       /\ UNCHANGED << Q, WakeAll, Upgrading >>
     ELSE
       /\ Q' = Append(Q, [tid |-> t, kind |-> Upread])
       /\ UNCHANGED << Lock, Mode, WakeAll, Upgrading >>

GrantHeadSingle ==
  /\ Len(Q) > 0
  /\ (WakeAll = FALSE \/ Q[1].kind # Read)
  /\ (
       (/\ Q[1].kind = Read
        /\ ~Lock.writer /\ ~Lock.beingUpgraded
        /\ Lock' = [Lock EXCEPT !.readers = @ + 1]
        /\ Mode' = [Mode EXCEPT ![Q[1].tid] = Read]
       )
     \/ (/\ Q[1].kind = Write
        /\ ~Lock.writer /\ ~Lock.upread /\ Lock.readers = 0 /\ ~Lock.beingUpgraded
        /\ Lock' = [Lock EXCEPT !.writer = TRUE]
        /\ Mode' = [Mode EXCEPT ![Q[1].tid] = Write]
       )
     \/ (/\ Q[1].kind = Upread
        /\ ~Lock.writer /\ ~Lock.upread
        /\ Lock' = [Lock EXCEPT !.upread = TRUE]
        /\ Mode' = [Mode EXCEPT ![Q[1].tid] = Upread]
       )
     )
  /\ Q' = Tail(Q)
  /\ WakeAll' = FALSE
  /\ UNCHANGED Upgrading

GrantReadersCohort ==
  /\ WakeAll
  /\ Len(Q) > 0
  /\ Q[1].kind = Read
  /\ ~Lock.writer /\ ~Lock.beingUpgraded
  /\ \E k \in 1..Len(Q):
       /\ \A i \in 1..k: Q[i].kind = Read
       /\ (IF k = Len(Q) THEN TRUE ELSE Q[k+1].kind # Read)  \* minimal fix: guard out-of-bounds access
       /\ LET S == { Q[i].tid : i \in 1..k } IN
            /\ Lock' = [Lock EXCEPT !.readers = @ + k]
            /\ Mode' = [ t \in Threads |-> IF t \in S THEN Read ELSE Mode[t] ]
            /\ Q' = IF k = Len(Q) THEN << >> ELSE SubSeq(Q, k+1, Len(Q))
            /\ WakeAll' = FALSE
            /\ UNCHANGED Upgrading

ReleaseRead(t) ==
  /\ t \in Threads
  /\ Mode[t] = Read
  /\ LET newReaders == Lock.readers - 1 IN
       /\ Lock' = [Lock EXCEPT !.readers = newReaders]
       /\ Mode' = [Mode EXCEPT ![t] = None]
       /\ WakeAll' = IF newReaders = 0 THEN FALSE ELSE WakeAll
       /\ UNCHANGED << Q, Upgrading >>

ReleaseWrite(t) ==
  /\ t \in Threads
  /\ Mode[t] = Write
  /\ Lock' = [Lock EXCEPT !.writer = FALSE]
  /\ Mode' = [Mode EXCEPT ![t] = None]
  /\ WakeAll' = TRUE
  /\ UNCHANGED << Q, Upgrading >>

ReleaseUpread(t) ==
  /\ t \in Threads
  /\ Mode[t] = Upread
  /\ ~Lock.beingUpgraded
  /\ Lock' = [Lock EXCEPT !.upread = FALSE]
  /\ Mode' = [Mode EXCEPT ![t] = None]
  /\ WakeAll' = IF (~Lock.writer /\ Lock.readers = 0) THEN TRUE ELSE WakeAll
  /\ UNCHANGED << Q, Upgrading >>

UpgradeStart(t) ==
  /\ t \in Threads
  /\ Mode[t] = Upread
  /\ Upgrading = Null
  /\ ~Lock.beingUpgraded
  /\ Lock' = [Lock EXCEPT !.beingUpgraded = TRUE]
  /\ Upgrading' = t
  /\ UNCHANGED << Q, Mode, WakeAll >>

UpgradeComplete(t) ==
  /\ t \in Threads
  /\ Upgrading = t
  /\ Mode[t] = Upread
  /\ Lock.beingUpgraded
  /\ Lock.readers = 0
  /\ Lock' = [Lock EXCEPT !.writer = TRUE, !.upread = FALSE, !.beingUpgraded = FALSE]
  /\ Mode' = [Mode EXCEPT ![t] = Write]
  /\ Upgrading' = Null
  /\ UNCHANGED << Q, WakeAll >>

Downgrade(t) ==
  /\ t \in Threads
  /\ Mode[t] = Write
  /\ Lock' = [Lock EXCEPT !.writer = FALSE, !.upread = TRUE]
  /\ Mode' = [Mode EXCEPT ![t] = Upread]
  /\ UNCHANGED << Q, WakeAll, Upgrading >>

Next ==
  \E t \in Threads:
    \/ RequestRead(t)
    \/ RequestWrite(t)
    \/ RequestUpread(t)
    \/ ReleaseRead(t)
    \/ ReleaseWrite(t)
    \/ ReleaseUpread(t)
    \/ UpgradeStart(t)
    \/ UpgradeComplete(t)
    \/ Downgrade(t)
  \/ GrantHeadSingle
  \/ GrantReadersCohort

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(GrantHeadSingle)
  /\ WF_vars(GrantReadersCohort)
  /\ \A t \in Threads: WF_vars(UpgradeComplete(t))

====