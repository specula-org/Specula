---- MODULE locksvc ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANT NumClients

Server == 0
Clients == 1..NumClients
Nodes == {Server} \cup Clients

MsgType == {"Lock", "Unlock", "Grant"}

MessageSet == { [type |-> t, from |-> n] : t \in MsgType /\ n \in Nodes }

Lock(c) == [type |-> "Lock", from |-> c]
Unlock(c) == [type |-> "Unlock", from |-> c]
Grant == [type |-> "Grant", from |-> Server]

EmptyBag == [m \in MessageSet |-> 0]
AddToBag(b, m) == [b EXCEPT ![m] = b[m] + 1]
RemoveFromBag(b, m) == [b EXCEPT ![m] = b[m] - 1]
BagHas(b, m) == b[m] > 0

ClientStates == {"idle", "waiting", "critical", "releasing"}

VARIABLES network, q, hasLock, cstate

TypeOK ==
  /\ q \in Seq(Clients)
  /\ hasLock \in [Clients -> BOOLEAN]
  /\ cstate \in [Clients -> ClientStates]
  /\ network \in [Nodes -> [MessageSet -> Nat]]

Init ==
  /\ TypeOK
  /\ q = << >>
  /\ hasLock = [c \in Clients |-> FALSE]
  /\ cstate = [c \in Clients |-> "idle"]
  /\ network = [n \in Nodes |-> EmptyBag]

ClientSendLock(c) ==
  /\ c \in Clients
  /\ cstate[c] = "idle"
  /\ network' = [network EXCEPT ![Server] = AddToBag(@, Lock(c))]
  /\ cstate' = [cstate EXCEPT ![c] = "waiting"]
  /\ UNCHANGED << q, hasLock >>

ClientRecvGrant(c) ==
  /\ c \in Clients
  /\ cstate[c] = "waiting"
  /\ BagHas(network[c], Grant)
  /\ network' = [network EXCEPT ![c] = RemoveFromBag(@, Grant)]
  /\ hasLock' = [hasLock EXCEPT ![c] = TRUE]
  /\ cstate' = [cstate EXCEPT ![c] = "critical"]
  /\ UNCHANGED q

ClientSendUnlock(c) ==
  /\ c \in Clients
  /\ cstate[c] = "critical"
  /\ hasLock[c] = TRUE
  /\ hasLock' = [hasLock EXCEPT ![c] = FALSE]
  /\ network' = [network EXCEPT ![Server] = AddToBag(@, Unlock(c))]
  /\ cstate' = [cstate EXCEPT ![c] = "releasing"]
  /\ UNCHANGED q

ClientReturnToIdle(c) ==
  /\ c \in Clients
  /\ cstate[c] = "releasing"
  /\ network[Server][Unlock(c)] = 0
  /\ cstate' = [cstate EXCEPT ![c] = "idle"]
  /\ UNCHANGED << q, hasLock, network >>

ServerRecvLock ==
  \E c \in Clients:
    /\ BagHas(network[Server], Lock(c))
    /\ q' = Append(q, c)
    /\ network' =
         IF Len(q) = 0
         THEN [network EXCEPT
                ![Server] = RemoveFromBag(@, Lock(c)),
                ![c] = AddToBag(@, Grant)]
         ELSE [network EXCEPT
                ![Server] = RemoveFromBag(@, Lock(c))]
    /\ UNCHANGED << hasLock, cstate >>

ServerRecvUnlockNoNext ==
  \E c \in Clients:
    /\ BagHas(network[Server], Unlock(c))
    /\ Len(q) = 1
    /\ q' = Tail(q)
    /\ network' = [network EXCEPT ![Server] = RemoveFromBag(@, Unlock(c))]
    /\ UNCHANGED << hasLock, cstate >>

ServerRecvUnlockGrantNext ==
  \E c \in Clients:
    /\ BagHas(network[Server], Unlock(c))
    /\ Len(q) >= 2
    /\ LET qNew == Tail(q) IN
         /\ q' = qNew
         /\ network' = [network EXCEPT
                          ![Server] = RemoveFromBag(@, Unlock(c)),
                          ![Head(qNew)] = AddToBag(@, Grant)]
    /\ UNCHANGED << hasLock, cstate >>

Next ==
  \/ ServerRecvLock
  \/ ServerRecvUnlockNoNext
  \/ ServerRecvUnlockGrantNext
  \/ \E c \in Clients: ClientSendLock(c)
  \/ \E c \in Clients: ClientRecvGrant(c)
  \/ \E c \in Clients: ClientSendUnlock(c)
  \/ \E c \in Clients: ClientReturnToIdle(c)

Vars == << network, q, hasLock, cstate >>

Spec ==
  Init /\ [][Next]_Vars
  /\ WF_Vars(ServerRecvLock)
  /\ WF_Vars(ServerRecvUnlockNoNext)
  /\ WF_Vars(ServerRecvUnlockGrantNext)
  /\ \A c \in Clients: WF_Vars(ClientRecvGrant(c))

====