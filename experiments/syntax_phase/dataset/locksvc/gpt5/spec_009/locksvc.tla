---- MODULE locksvc ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANT NumClients

Clients == 1..NumClients
Server == 0
Nodes == {Server} \cup Clients

LockMsg == 1
UnlockMsg == 2
GrantMsg == 3

ReqMsg == [from: Clients, type: {LockMsg, UnlockMsg}]
Msg == {GrantMsg} \cup ReqMsg

VARIABLES q, Net, hasLock, pc

TypeOK ==
  /\ q \in Seq(Clients)
  /\ Net \in [Nodes -> Bag(Msg)]
  /\ hasLock \in [Clients -> BOOLEAN]
  /\ pc \in [Clients -> {"Start", "Wait", "Critical", "Done"}]

Init ==
  /\ q = << >>
  /\ Net = [n \in Nodes |-> [m \in Msg |-> 0]]
  /\ hasLock = [c \in Clients |-> FALSE]
  /\ pc = [c \in Clients |-> "Start"]

ClientSendLock(c) ==
  /\ c \in Clients
  /\ pc[c] = "Start"
  /\ Net' = [Net EXCEPT ![Server][[from |-> c, type |-> LockMsg]] = @ + 1]
  /\ pc' = [pc EXCEPT ![c] = "Wait"]
  /\ UNCHANGED << q, hasLock >>

ClientWaitGrant(c) ==
  /\ c \in Clients
  /\ pc[c] = "Wait"
  /\ Net[c][GrantMsg] > 0
  /\ Net' = [Net EXCEPT ![c][GrantMsg] = @ - 1]
  /\ hasLock' = [hasLock EXCEPT ![c] = TRUE]
  /\ pc' = [pc EXCEPT ![c] = "Critical"]
  /\ UNCHANGED q

ClientUnlock(c) ==
  /\ c \in Clients
  /\ pc[c] = "Critical"
  /\ hasLock' = [hasLock EXCEPT ![c] = FALSE]
  /\ Net' = [Net EXCEPT ![Server][[from |-> c, type |-> UnlockMsg]] = @ + 1]
  /\ pc' = [pc EXCEPT ![c] = "Done"]
  /\ UNCHANGED q

ServerRecvLock(c) ==
  /\ c \in Clients
  /\ Net[Server][[from |-> c, type |-> LockMsg]] > 0
  /\ LET grantNeeded == (q = << >>)
     IN /\ Net' =
           [Net EXCEPT
             ![Server][[from |-> c, type |-> LockMsg]] = @ - 1,
             ![c][GrantMsg] = IF grantNeeded THEN @ + 1 ELSE @
           ]
        /\ q' = Append(q, c)
        /\ UNCHANGED << hasLock, pc >>

ServerRecvUnlock(c) ==
  /\ c \in Clients
  /\ Net[Server][[from |-> c, type |-> UnlockMsg]] > 0
  /\ q # << >> /\ Head(q) = c
  /\ LET qNew == Tail(q)
     IN /\ Net' =
            IF qNew = << >> THEN
               [Net EXCEPT ![Server][[from |-> c, type |-> UnlockMsg]] = @ - 1]
            ELSE
               [Net EXCEPT
                 ![Server][[from |-> c, type |-> UnlockMsg]] = @ - 1,
                 ![Head(qNew)][GrantMsg] = @ + 1
               ]
        /\ q' = qNew
        /\ UNCHANGED << hasLock, pc >>

Next ==
  \E c \in Clients:
       ClientSendLock(c)
    \/ ClientWaitGrant(c)
    \/ ClientUnlock(c)
    \/ ServerRecvLock(c)
    \/ ServerRecvUnlock(c)

Vars == << q, Net, hasLock, pc >>

Spec ==
  Init
  /\ [] [Next]_Vars
  /\ WF_Vars(Next)

====