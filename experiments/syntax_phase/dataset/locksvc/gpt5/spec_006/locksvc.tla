---- MODULE locksvc ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANT NumClients

ASSUME /\ NumClients \in Nat
       /\ NumClients >= 1

Server == 0
Clients == 1..NumClients
Nodes == {Server} \cup Clients

Lock == 1
Unlock == 2
Grant == 3

LockReq(c) == [type |-> Lock, from |-> c]
UnlockReq(c) == [type |-> Unlock, from |-> c]

ServerMsgs == { LockReq(c) : c \in Clients } \cup { UnlockReq(c) : c \in Clients }
ClientMsgs == {Grant}

EmptyBag(S) == [m \in S |-> 0]
Add(b, m) == [b EXCEPT ![m] = @ + 1]
Remove(b, m) == [b EXCEPT ![m] = @ - 1]
IsBagOver(b, S) == DOMAIN b = S /\ \A m \in S: b[m] \in Nat

VARIABLES q, hasLock, pc, network

Vars == << q, hasLock, pc, network >>

TypeOK ==
  /\ q \in Seq(Clients)
  /\ hasLock \in [Clients -> BOOLEAN]
  /\ pc \in [Clients -> {"start", "wait", "cs", "done"}]
  /\ network \in [Nodes -> [IF _ = Server THEN ServerMsgs ELSE ClientMsgs -> Nat]]
  /\ \A n \in Nodes:
       IF n = Server
         THEN IsBagOver(network[n], ServerMsgs)
         ELSE IsBagOver(network[n], ClientMsgs)

Init ==
  /\ q = << >>
  /\ hasLock = [c \in Clients |-> FALSE]
  /\ pc = [c \in Clients |-> "start"]
  /\ network =
       [n \in Nodes |->
          IF n = Server
            THEN EmptyBag(ServerMsgs)
            ELSE EmptyBag(ClientMsgs)]

ClientSendLock(c) ==
  /\ c \in Clients
  /\ pc[c] = "start"
  /\ network' = [network EXCEPT ![Server] = Add(@, LockReq(c))]
  /\ pc' = [pc EXCEPT ![c] = "wait"]
  /\ UNCHANGED << q, hasLock >>

ClientRecvGrant(c) ==
  /\ c \in Clients
  /\ pc[c] = "wait"
  /\ network[c][Grant] > 0
  /\ network' = [network EXCEPT ![c] = Remove(@, Grant)]
  /\ hasLock' = [hasLock EXCEPT ![c] = TRUE]
  /\ pc' = [pc EXCEPT ![c] = "cs"]
  /\ UNCHANGED q

ClientUnlock(c) ==
  /\ c \in Clients
  /\ pc[c] = "cs"
  /\ hasLock[c] = TRUE
  /\ network' = [network EXCEPT ![Server] = Add(@, UnlockReq(c))]
  /\ hasLock' = [hasLock EXCEPT ![c] = FALSE]
  /\ pc' = [pc EXCEPT ![c] = "done"]
  /\ UNCHANGED q

ServerRecvLock ==
  \E c \in Clients:
    /\ network[Server][LockReq(c)] > 0
    /\ IF q = << >>
         THEN /\ network' =
                  [network EXCEPT
                    ![Server] = Remove(@, LockReq(c)),
                    ![c] = Add(@, Grant)]
              /\ q' = Append(q, c)
         ELSE /\ network' =
                  [network EXCEPT
                    ![Server] = Remove(@, LockReq(c))]
              /\ q' = Append(q, c)
    /\ UNCHANGED << hasLock, pc >>

ServerRecvUnlock ==
  \E c \in Clients:
    /\ network[Server][UnlockReq(c)] > 0
    /\ q # << >> /\ Head(q) = c
    /\ LET net1 == [network EXCEPT ![Server] = Remove(@, UnlockReq(c))]
       IN IF Tail(q) = << >>
            THEN /\ network' = net1
                 /\ q' = Tail(q)
            ELSE /\ network' =
                     [net1 EXCEPT ![Head(Tail(q))] = Add(@, Grant)]
                 /\ q' = Tail(q)
    /\ UNCHANGED << hasLock, pc >>

Next ==
  \/ \E c \in Clients: ClientSendLock(c)
  \/ \E c \in Clients: ClientRecvGrant(c)
  \/ \E c \in Clients: ClientUnlock(c)
  \/ ServerRecvLock
  \/ ServerRecvUnlock

Spec ==
  Init /\ [][Next]_Vars
  /\ (\A c \in Clients: WF_Vars(ClientSendLock(c)))
  /\ (\A c \in Clients: WF_Vars(ClientRecvGrant(c)))
  /\ (\A c \in Clients: WF_Vars(ClientUnlock(c)))
  /\ WF_Vars(ServerRecvLock)
  /\ WF_Vars(ServerRecvUnlock)

====