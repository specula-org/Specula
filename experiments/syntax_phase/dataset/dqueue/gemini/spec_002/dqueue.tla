---- MODULE etcdraft ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANT NumClients
ASSUME NumClients \in Nat \ {0}

Server == 0
Client == 1..NumClients
Node == {Server} \cup Client

LockMsgType == "request"
UnlockMsgType == "release"
GrantMsgType == "grant"

RequestMsg(c) == [type |-> LockMsgType, from |-> c]
ReleaseMsg(c) == [type |-> UnlockMsgType, from |-> c]
GrantMsg(c) == [type |-> GrantMsgType, to |-> c]

VARIABLES pc, q, network, hasLock, msg

vars == <<pc, q, network, hasLock, msg>>

Init ==
    /\ pc = [n \in Node |-> IF n = Server THEN "serverLoop" ELSE "c"]
    /\ q = <<>>
    /\ network = [n \in Node |-> <<>>]
    /\ hasLock = [c \in Client |-> FALSE]
    /\ msg = "InitValue"

ClientRequest(c) ==
    /\ pc[c] = "c"
    /\ pc' = [pc EXCEPT ![c] = "c1"]
    /\ network' = [network EXCEPT ![Server] = Append(@, RequestMsg(c))]
    /\ UNCHANGED <<q, hasLock, msg>>

ClientReceiveGrant(c) ==
    /\ pc[c] = "c1"
    /\ network[c] # <<>>
    /\ Head(network[c]).type = GrantMsgType
    /\ pc' = [pc EXCEPT ![c] = "p"]
    /\ network' = [network EXCEPT ![c] = Tail(@)]
    /\ UNCHANGED <<q, hasLock, msg>>

ClientStartCS(c) ==
    /\ pc[c] = "p"
    /\ pc' = [pc EXCEPT ![c] = "p1"]
    /\ hasLock' = [hasLock EXCEPT ![c] = TRUE]
    /\ UNCHANGED <<q, network, msg>>

ClientFinishCS(c) ==
    /\ pc[c] = "p1"
    /\ pc' = [pc EXCEPT ![c] = "p2"]
    /\ UNCHANGED <<q, network, hasLock, msg>>

ClientUnlock(c) ==
    /\ pc[c] = "p2"
    /\ pc' = [pc EXCEPT ![c] = "c2"]
    /\ hasLock' = [hasLock EXCEPT ![c] = FALSE]
    /\ network' = [network EXCEPT ![Server] = Append(@, ReleaseMsg(c))]
    /\ UNCHANGED <<q, msg>>

ClientReset(c) ==
    /\ pc[c] = "c2"
    /\ pc' = [pc EXCEPT ![c] = "c"]
    /\ UNCHANGED <<q, network, hasLock, msg>>

AClient(c) ==
    \/ ClientRequest(c)
    \/ ClientReceiveGrant(c)
    \/ ClientStartCS(c)
    \/ ClientFinishCS(c)
    \/ ClientUnlock(c)
    \/ ClientReset(c)

ServerReceive ==
    /\ pc[Server] = "serverLoop"
    /\ network[Server] # <<>>
    /\ pc' = [pc EXCEPT ![Server] = "serverRespond"]
    /\ msg' = Head(network[Server])
    /\ network' = [network EXCEPT ![Server] = Tail(@)]
    /\ UNCHANGED <<q, hasLock>>

ServerRespond ==
    /\ pc[Server] = "serverRespond"
    /\ pc' = [pc EXCEPT ![Server] = "serverLoop"]
    /\ IF msg.type = LockMsgType
       THEN /\ q' = Append(q, msg.from)
            /\ network' = IF q = <<>>
                          THEN [network EXCEPT ![msg.from] = Append(@, GrantMsg(msg.from))]
                          ELSE network
       ELSE /\ msg.type = UnlockMsgType
            /\ q # <<>>
            /\ LET new_q == Tail(q)
               IN /\ q' = new_q
                  /\ network' = IF new_q # <<>>
                                THEN [network EXCEPT ![Head(new_q)] = Append(@, GrantMsg(Head(new_q)))]
                                ELSE network
    /\ UNCHANGED <<hasLock, msg>>

AServer == ServerReceive \/ ServerRespond

Next ==
    \/ AServer
    \/ \E c \in Client : AClient(c)

Spec == Init /\ [][Next]_vars

====