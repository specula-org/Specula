---- MODULE locksvc ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANT NumClients

ServerID == 0
ServerSet == {ServerID}
ClientSet == 1..NumClients
NodeSet == ServerSet \cup ClientSet

MsgType == {"Lock", "Unlock", "Grant"}
Messages == [type: MsgType, from: NodeSet]

EmpBag == [m \in Messages |-> 0]
Add(b, m) == [b EXCEPT ![m] = b[m] + 1]
Rem(b, m) == [b EXCEPT ![m] = b[m] - 1]

LockMsg(c) == [type |-> "Lock", from |-> c]
UnlockMsg(c) == [type |-> "Unlock", from |-> c]
GrantMsg == [type |-> "Grant", from |-> ServerID]

VARIABLES network, q, hasLock, phase

Vars == << network, q, hasLock, phase >>

TypeOK ==
  /\ hasLock \in [ClientSet -> BOOLEAN]
  /\ phase \in [ClientSet -> {"start", "acq", "crit", "done"}]
  /\ q \in Seq(ClientSet)
  /\ network \in [NodeSet -> [Messages -> Nat]]

Init ==
  /\ hasLock = [c \in ClientSet |-> FALSE]
  /\ phase = [c \in ClientSet |-> "start"]
  /\ q = << >>
  /\ network = [n \in NodeSet |-> EmpBag]

SendLock(c) ==
  /\ c \in ClientSet
  /\ phase[c] = "start"
  /\ network' = [network EXCEPT ![ServerID] = Add(@, LockMsg(c))]
  /\ phase' = [phase EXCEPT ![c] = "acq"]
  /\ UNCHANGED << q, hasLock >>

ClientRecvGrant(c) ==
  /\ c \in ClientSet
  /\ phase[c] = "acq"
  /\ \E m \in Messages:
       /\ m.type = "Grant"
       /\ network[c][m] > 0
       /\ network' = [network EXCEPT ![c] = Rem(@, m)]
  /\ phase' = [phase EXCEPT ![c] = "crit"]
  /\ hasLock' = [hasLock EXCEPT ![c] = TRUE]
  /\ UNCHANGED q

ClientRelease(c) ==
  /\ c \in ClientSet
  /\ phase[c] = "crit"
  /\ network' = [network EXCEPT ![ServerID] = Add(@, UnlockMsg(c))]
  /\ hasLock' = [hasLock EXCEPT ![c] = FALSE]
  /\ phase' = [phase EXCEPT ![c] = "done"]
  /\ UNCHANGED q

ServerReceiveLock ==
  \E m \in Messages:
    /\ m.type = "Lock"
    /\ m.from \in ClientSet
    /\ network[ServerID][m] > 0
    /\ network' =
         IF Len(q) = 0
           THEN [ network EXCEPT
                    ![ServerID] = Rem(@, m),
                    ![m.from]   = Add(@, GrantMsg)
                ]
           ELSE [ network EXCEPT
                    ![ServerID] = Rem(@, m)
                ]
    /\ q' = Append(q, m.from)
    /\ UNCHANGED << hasLock, phase >>

ServerReceiveUnlock ==
  \E m \in Messages:
    /\ m.type = "Unlock"
    /\ m.from \in ClientSet
    /\ network[ServerID][m] > 0
    /\ q \neq << >>
    /\ LET qAfter == Tail(q) IN
         /\ network' =
              IF qAfter = << >>
                THEN [ network EXCEPT ![ServerID] = Rem(@, m) ]
                ELSE [ network EXCEPT
                         ![ServerID]           = Rem(@, m),
                         ![Head(qAfter)]       = Add(@, GrantMsg)
                     ]
         /\ q' = qAfter
  /\ UNCHANGED << hasLock, phase >>

Next ==
  \/ (\E c \in ClientSet: SendLock(c))
  \/ (\E c \in ClientSet: ClientRecvGrant(c))
  \/ (\E c \in ClientSet: ClientRelease(c))
  \/ ServerReceiveLock
  \/ ServerReceiveUnlock

Spec ==
  Init /\ [][Next]_Vars /\
  /\ \A c \in ClientSet: WF_Vars(SendLock(c))
  /\ \A c \in ClientSet: WF_Vars(ClientRecvGrant(c))
  /\ \A c \in ClientSet: WF_Vars(ClientRelease(c))
  /\ WF_Vars(ServerReceiveLock)
  /\ WF_Vars(ServerReceiveUnlock)

====