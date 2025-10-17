---- MODULE rwmutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANT THREADS

KIND == {"read","write","upread"}
PCVals == {"Idle","WaitingRead","Reading","WaitingWrite","Writing","WaitingUpread","Upreading","Upgrading"}

VARIABLES pc, writer, upread, upgrading, readers, Q, awoken

Req(e) == e \in [t: THREADS, k: KIND]
DomainQ == DOMAIN Q
Head(Qs) == Qs[1]
IsInQ(Qs, t) == \E i \in DomainQ: Qs[i].t = t
IndexOf(Qs, t) == CHOOSE i \in DomainQ: Qs[i].t = t
RemoveAt(Qs, i) == SubSeq(Qs, 1, i-1) \o SubSeq(Qs, i+1, Len(Qs))
AllPrevReaders(Qs, i) == \A j \in 1..(i-1): Qs[j].k = "read"
QThreads(Qs) == { Qs[i].t : i \in DomainQ }

TypeOK ==
  /\ pc \in [THREADS -> PCVals]
  /\ writer \in BOOLEAN
  /\ upread \in BOOLEAN
  /\ upgrading \in BOOLEAN
  /\ readers \in Nat
  /\ Q \in Seq([t: THREADS, k: KIND])
  /\ awoken \subseteq THREADS

Init ==
  /\ pc = [t \in THREADS |-> "Idle"]
  /\ writer = FALSE
  /\ upread = FALSE
  /\ upgrading = FALSE
  /\ readers = 0
  /\ Q = << >>
  /\ awoken = {}

ReadCall(t) ==
  /\ t \in THREADS
  /\ pc[t] = "Idle"
  /\ IF ~writer /\ ~upgrading
        THEN /\ pc' = [pc EXCEPT ![t] = "Reading"]
             /\ readers' = readers + 1
             /\ UNCHANGED <<writer, upread, upgrading, Q, awoken>>
        ELSE /\ ~IsInQ(Q, t)
             /\ Q' = Q \o <<[t |-> t, k |-> "read"]>>
             /\ pc' = [pc EXCEPT ![t] = "WaitingRead"]
             /\ UNCHANGED <<writer, upread, upgrading, readers, awoken>>

WriteCall(t) ==
  /\ t \in THREADS
  /\ pc[t] = "Idle"
  /\ IF ~writer /\ ~upread /\ readers = 0
        THEN /\ writer' = TRUE
             /\ pc' = [pc EXCEPT ![t] = "Writing"]
             /\ UNCHANGED <<upread, upgrading, readers, Q, awoken>>
        ELSE /\ ~IsInQ(Q, t)
             /\ Q' = Q \o <<[t |-> t, k |-> "write"]>>
             /\ pc' = [pc EXCEPT ![t] = "WaitingWrite"]
             /\ UNCHANGED <<writer, upread, upgrading, readers, awoken>>

UpreadCall(t) ==
  /\ t \in THREADS
  /\ pc[t] = "Idle"
  /\ IF ~writer /\ ~upread
        THEN /\ upread' = TRUE
             /\ pc' = [pc EXCEPT ![t] = "Upreading"]
             /\ UNCHANGED <<writer, upgrading, readers, Q, awoken>>
        ELSE /\ ~IsInQ(Q, t)
             /\ Q' = Q \o <<[t |-> t, k |-> "upread"]>>
             /\ pc' = [pc EXCEPT ![t] = "WaitingUpread"]
             /\ UNCHANGED <<writer, upread, upgrading, readers, awoken>>

AcquireReadFromQueue(t) ==
  /\ t \in THREADS
  /\ pc[t] = "WaitingRead"
  /\ t \in awoken
  /\ LET i == IndexOf(Q, t) IN
       /\ Q[i].k = "read"
       /\ AllPrevReaders(Q, i)
       /\ ~writer /\ ~upgrading
       /\ readers' = readers + 1
       /\ Q' = RemoveAt(Q, i)
       /\ awoken' = awoken \ {t}
       /\ pc' = [pc EXCEPT ![t] = "Reading"]
       /\ UNCHANGED <<writer, upread, upgrading>>

AcquireWriteFromQueue(t) ==
  /\ t \in THREADS
  /\ pc[t] = "WaitingWrite"
  /\ t \in awoken
  /\ Q # << >> /\ Q[1].t = t /\ Q[1].k = "write"
  /\ ~writer /\ ~upread /\ readers = 0
  /\ writer' = TRUE
  /\ Q' = RemoveAt(Q, 1)
  /\ awoken' = awoken \ {t}
  /\ pc' = [pc EXCEPT ![t] = "Writing"]
  /\ UNCHANGED <<upread, upgrading, readers>>

AcquireUpreadFromQueue(t) ==
  /\ t \in THREADS
  /\ pc[t] = "WaitingUpread"
  /\ t \in awoken
  /\ Q # << >> /\ Q[1].t = t /\ Q[1].k = "upread"
  /\ ~writer /\ ~upread
  /\ upread' = TRUE
  /\ Q' = RemoveAt(Q, 1)
  /\ awoken' = awoken \ {t}
  /\ pc' = [pc EXCEPT ![t] = "Upreading"]
  /\ UNCHANGED <<writer, upgrading, readers>>

ReadRelease(t) ==
  /\ t \in THREADS
  /\ pc[t] = "Reading"
  /\ readers > 0
  /\ readers' = readers - 1
  /\ pc' = [pc EXCEPT ![t] = "Idle"]
  /\ IF readers' = 0 /\ Len(Q) > 0
        THEN /\ awoken' = awoken \cup { Q[1].t }
        ELSE /\ awoken' = awoken
  /\ UNCHANGED <<writer, upread, upgrading, Q>>

WriteRelease(t) ==
  /\ t \in THREADS
  /\ pc[t] = "Writing"
  /\ writer = TRUE
  /\ writer' = FALSE
  /\ awoken' = awoken \cup QThreads(Q)
  /\ pc' = [pc EXCEPT ![t] = "Idle"]
  /\ UNCHANGED <<upread, upgrading, readers, Q>>

UpreadRelease(t) ==
  /\ t \in THREADS
  /\ pc[t] = "Upreading"
  /\ upread = TRUE
  /\ upgrading = FALSE
  /\ upread' = FALSE
  /\ awoken' = awoken \cup QThreads(Q)
  /\ pc' = [pc EXCEPT ![t] = "Idle"]
  /\ UNCHANGED <<writer, upgrading, readers, Q>>

WriteToUpread(t) ==
  /\ t \in THREADS
  /\ pc[t] = "Writing"
  /\ writer = TRUE
  /\ writer' = FALSE
  /\ upread' = TRUE
  /\ awoken' = awoken \cup QThreads(Q)
  /\ pc' = [pc EXCEPT ![t] = "Upreading"]
  /\ UNCHANGED <<upgrading, readers, Q>>

UpgradeStart(t) ==
  /\ t \in THREADS
  /\ pc[t] = "Upreading"
  /\ upgrading = FALSE
  /\ upgrading' = TRUE
  /\ pc' = [pc EXCEPT ![t] = "Upgrading"]
  /\ UNCHANGED <<writer, upread, readers, Q, awoken>>

UpgradeCommit(t) ==
  /\ t \in THREADS
  /\ pc[t] = "Upgrading"
  /\ readers = 0
  /\ writer = FALSE
  /\ writer' = TRUE
  /\ upread' = FALSE
  /\ upgrading' = FALSE
  /\ pc' = [pc EXCEPT ![t] = "Writing"]
  /\ UNCHANGED <<readers, Q, awoken>>

Next ==
  \E t \in THREADS:
    \/ ReadCall(t)
    \/ WriteCall(t)
    \/ UpreadCall(t)
    \/ AcquireReadFromQueue(t)
    \/ AcquireWriteFromQueue(t)
    \/ AcquireUpreadFromQueue(t)
    \/ ReadRelease(t)
    \/ WriteRelease(t)
    \/ UpreadRelease(t)
    \/ WriteToUpread(t)
    \/ UpgradeStart(t)
    \/ UpgradeCommit(t)

Vars == <<pc, writer, upread, upgrading, readers, Q, awoken>>

Spec ==
  /\ Init
  /\ [][Next]_Vars
  /\ \A t \in THREADS:
       /\ WF_Vars(AcquireReadFromQueue(t) \/ AcquireWriteFromQueue(t) \/ AcquireUpreadFromQueue(t))
       /\ WF_Vars(UpgradeCommit(t))

====