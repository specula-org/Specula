---- MODULE locksvc ----
EXTENDS TLC, Sequences, Naturals, FiniteSets, Bags
CONSTANTS NumClients, LockMsg, UnlockMsg, GrantMsg
Clients == 1..NumClients
Server == 0
Nodes == Server \cup Clients
VARIABLES hasLock, serverQueue, network
vars == <<hasLock, serverQueue, network>>
Init == 
    /\ hasLock = [c \in Clients |-> FALSE]
    /\ serverQueue = << >>
    /\ network = [n \in Nodes |-> EmptyBag]
SendLock(c) ==
    /\ hasLock[c] = FALSE
    /\ network' = [network EXCEPT ![Server] = Bags!Add([type |-> LockMsg, from |-> c], @)]
    /\ UNCHANGED <<hasLock, serverQueue>>
SendUnlock(c) ==
    /\ hasLock[c] = TRUE
    /\ hasLock' = [hasLock EXCEPT ![c] = FALSE]
    /\ network' = [network EXCEPT ![Server] = Bags!Add([type |-> UnlockMsg, from |-> c], @)]
    /\ UNCHANGED serverQueue
ReceiveLock ==
    /\ \E msg \in BagToSet(network[Server]) : msg.type = LockMsg
    /\ LET msg == CHOOSE msg \in BagToSet(network[Server]) : msg.type = LockMsg
       IN
       IF serverQueue = << >> THEN
           /\ network' = [network EXCEPT ![Server] = Bags!Remove(msg, @), ![msg.from] = Bags!Add([type |-> GrantMsg, from |-> Server], @)]
           /\ serverQueue' = serverQueue
       ELSE
           /\ network' = [network EXCEPT ![Server] = Bags!Remove(msg, @)]
           /\ serverQueue' = Append(serverQueue, msg.from)
    /\ UNCHANGED hasLock
ReceiveUnlock ==
    /\ \E msg \in BagToSet(network[Server]) : msg.type = UnlockMsg
    /\ LET msg == CHOOSE msg \in BagToSet(network[Server]) : msg.type = UnlockMsg
       IN
       /\ serverQueue' = Tail(serverQueue)
       /\ IF serverQueue' /= << >> THEN
             network' = [network EXCEPT ![Server] = Bags!Remove(msg, @), ![Head(serverQueue')] = Bags!Add([type |-> GrantMsg, from |-> Server], @)]
          ELSE
             network' = [network EXCEPT ![Server] = Bags!Remove(msg, @)]
    /\ UNCHANGED hasLock
ReceiveGrant(c) ==
    /\ \E msg \in BagToSet(network[c]) : msg.type = GrantMsg
    /\ LET msg == CHOOSE msg \in BagToSet(network[c]) : msg.type = GrantMsg
       IN
       /\ network' = [network EXCEPT ![c] = Bags!Remove(msg, @)]
       /\ hasLock' = [hasLock EXCEPT ![c] = TRUE]
       /\ UNCHANGED serverQueue
Next == 
    \/ \E c \in Clients : SendLock(c)
    \/ \E c \in Clients : SendUnlock(c)
    \/ ReceiveLock
    \/ ReceiveUnlock
    \/ \E c \in Clients : ReceiveGrant(c)
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
====