---- MODULE locksvc ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS NumClients, Server
VARIABLES net, q, hasLock

LockMsg == 1
UnlockMsg == 2
GrantMsg == 3
NodeSet == {Server} \union (1..NumClients)
Message == [type: {LockMsg, UnlockMsg, GrantMsg}, from: NodeSet]

TypeOK ==
    /\ net \in [NodeSet -> BAG(Message)]
    /\ q \in Seq(1..NumClients)
    /\ hasLock \in [1..NumClients -> BOOLEAN]

Init ==
    /\ net = [n \in NodeSet |-> EmptyBag]
    /\ q = <<>>
    /\ hasLock = [c \in 1..NumClients |-> FALSE]

ServerReceive ==
    \E msg \in net[Server]:
        LET newNet == [net EXCEPT ![Server] = net[Server] \ {msg}]
        IN
        \/ /\ msg.type = LockMsg
           /\ q' = Append(q, msg.from)
           /\ IF q = <<>> THEN
                 net' = [newNet EXCEPT ![msg.from] = newNet[msg.from] \cup [type |-> GrantMsg, from |-> Server]]
              ELSE
                 net' = newNet
        \/ /\ msg.type = UnlockMsg
           /\ q' = Tail(q)
           /\ IF q' /= <<>> THEN
                 net' = [newNet EXCEPT ![Head(q')] = newNet[Head(q')] \cup [type |-> GrantMsg, from |-> Server]]
              ELSE
                 net' = newNet

ClientSendLock(self) ==
    /\ hasLock[self] = FALSE
    /\ self \notin q
    /\ net' = [net EXCEPT ![Server] = net[Server] \cup [type |-> LockMsg, from |-> self]]
    /\ UNCHANGED <<q, hasLock>>

ClientReceiveGrant(self) ==
    \E msg \in net[self]:
        /\ msg.type = GrantMsg
        /\ hasLock' = [hasLock EXCEPT ![self] = TRUE]
        /\ net' = [net EXCEPT ![self] = net[self] \ {msg}]
        /\ UNCHANGED q

ClientUnlock(self) ==
    /\ hasLock[self] = TRUE
    /\ net' = [net EXCEPT ![Server] = net[Server] \cup [type |-> UnlockMsg, from |-> self]]
    /\ hasLock' = [hasLock EXCEPT ![self] = FALSE]
    /\ UNCHANGED q

Next ==
    \/ \E self \in 1..NumClients: ClientSendLock(self)
    \/ \E self \in 1..NumClients: ClientReceiveGrant(self)
    \/ \E self \in 1..NumClients: ClientUnlock(self)
    \/ ServerReceive

Spec ==
    Init
    /\ [][Next]_<<net, q, hasLock>>
    /\ WF_<<net, q, hasLock>>(ServerReceive)
    /\ \A self \in 1..NumClients: WF_<<net, q, hasLock>>(ClientReceiveGrant(self))
    /\ \A self \in 1..NumClients: WF_<<net, q, hasLock>>(ClientUnlock(self))

====