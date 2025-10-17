---- MODULE locksvc ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS NumClients, Server
VARIABLES net, q, hasLock

LockMsg == 1
UnlockMsg == 2
GrantMsg == 3
NodeSet == {{Server}} \union (1..NumClients)
Message == [type: {{LockMsg, UnlockMsg, GrantMsg}}, from: NodeSet]

TypeOK ==
    /\ net \in [NodeSet -> Bag(Message)]
    /\ q \in Seq(1..NumClients)
    /\ hasLock \in [1..NumClients -> BOOLEAN]

Init ==
    /\ net = [n \in NodeSet |-> EmptyBag]
    /\ q = <<>>
    /\ hasLock = [c \in 1..NumClients |-> FALSE]

ServerReceive ==
    \E msg \in net[Server]:
        LET newNet == [net EXCEPT ![Server] = net[Server] \ {{msg}}]
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

ClientSendLock(c) ==
    /\ hasLock[c] = FALSE
    /\ c \notin q
    /\ net' = [net EXCEPT ![Server] = net[Server] \cup [type |-> LockMsg, from |-> c]]
    /\ UNCHANGED <<q, hasLock>>

ClientReceiveGrant(c) ==
    \E msg \in net[c]:
        /\ msg.type = GrantMsg
        /\ hasLock' = [hasLock EXCEPT ![c] = TRUE]
        /\ net' = [net EXCEPT ![c] = net[c] \ {{msg}}]
        /\ UNCHANGED q

ClientUnlock(c) ==
    /\ hasLock[c] = TRUE
    /\ net' = [net EXCEPT ![Server] = net[Server] \cup [type |-> UnlockMsg, from |-> c]]
    /\ hasLock' = [hasLock EXCEPT ![c] = FALSE]
    /\ UNCHANGED q

Next ==
    \/ \E c \in 1..NumClients: ClientSendLock(c)
    \/ \E c \in 1..NumClients: ClientReceiveGrant(c)
    \/ \E c \in 1..NumClients: ClientUnlock(c)
    \/ ServerReceive

Spec ==
    Init
    /\ [][Next]_<<net, q, hasLock>>
    /\ WF_<<net, q, hasLock>>(Next)

====