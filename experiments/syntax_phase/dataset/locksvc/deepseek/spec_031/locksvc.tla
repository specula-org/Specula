---- MODULE locksvc ----
EXTENDS TLC, Sequences, Naturals, FiniteSets, Bags
CONSTANTS NumClients, LockMsg, UnlockMsg, GrantMsg
Clients == 1..NumClients
Server == {0}
Nodes == Server \cup Clients
VARIABLES hasLock, serverQueue, network
vars == <<hasLock, serverQueue, network>>
SingletonBag(e) == [x \in {e} |-> 1]
Init == 
    /\ hasLock = [c \in Clients |-> FALSE]
    /\ serverQueue = << >>
    /\ network = [n \in Nodes |-> EmptyBag]
SendLock(c) ==
    /\ hasLock[c] = FALSE
    /\ network' = [network EXCEPT ![Server] = BagUnion(@, SingletonBag([type |-> LockMsg, from |-> c]))]
    /\ UNCHANGED <<hasLock, serverQueue>>
SendUnlock(c) ==
    /\ hasLock[c] = TRUE
    /\ hasLock' = [hasLock EXCEPT ![c] = FALSE]
    /\ network' = [network EXCEPT ![Server] = BagUnion(@, SingletonBag([type |-> UnlockMsg, from |-> c]))]
    /\ UNCHANGED serverQueue
ReceiveLock ==
    /\ \E msg \in BagToSet(network[Server]) : msg.type = LockMsg
    /\ LET msg == CHOOSE msg \in BagToSet(network[Server]) : msg.type = LockMsg
       IN
       IF serverQueue = << >> THEN
           /\ network' = [network EXCEPT ![Server] = BagDiff(@, SingletonBag(msg)),
                                   ![msg.from] = BagUnion(@, SingletonBag([type |-> GrantMsg, from |-> Server]))]
           /\ serverQueue' = serverQueue
       ELSE
           /\ network' = [network EXCEPT ![Server] = BagDiff(@, SingletonBag(msg))]
           /\ serverQueue' = Append(serverQueue, msg.from)
    /\ UNCHANGED hasLock
ReceiveUnlock ==
    /\ \E msg \in BagToSet(network[Server]) : msg.type = UnlockMsg
    /\ LET msg == CHOOSE msg \in BagToSet(network[Server]) : msg.type = UnlockMsg
       IN
       IF serverQueue = << >> THEN
           /\ serverQueue' = serverQueue
           /\ network' = [network EXCEPT ![Server] = BagDiff(@, SingletonBag(msg))]
       ELSE
           /\ serverQueue' = Tail(serverQueue)
           /\ network' = [network EXCEPT ![Server] = BagDiff(@, SingletonBag(msg)),
                                   ![Head(serverQueue)] = BagUnion(@, SingletonBag([type |-> GrantMsg, from |-> Server]))]
    /\ UNCHANGED hasLock
ReceiveGrant(c) ==
    /\ \E msg \in BagToSet(network[c]) : msg.type = GrantMsg
    /\ LET msg == CHOOSE msg \in BagToSet(network[c]) : msg.type = GrantMsg
       IN
       /\ network' = [network EXCEPT ![c] = BagDiff(@, SingletonBag(msg))]
       /\ hasLock' = [hasLock EXCEPT ![c] = TRUE]
       /\ UNCHANGED serverQueue
Next == 
    \/ \E c \in Clients : SendLock(c)
    \/ \E c \in Clients : SendUnlock(c)
    \/ ReceiveLock
    \/ ReceiveUnlock
    \/ \E c \in Clients : ReceiveGrant(c)
Spec == Init /\ [][Next]_vars /\ 
        (\A c \in Clients : WF_vars(SendLock(c))) /\ 
        (\A c \in Clients : WF_vars(SendUnlock(c))) /\ 
        WF_vars(ReceiveLock) /\ 
        WF_vars(ReceiveUnlock) /\ 
        (\A c \in Clients : WF_vars(ReceiveGrant(c)))
====