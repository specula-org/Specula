---- MODULE locksvc ----
EXTENDS Naturals, Sequences, FiniteSets, Bags
CONSTANTS NumClients, LockMsg, UnlockMsg, GrantMsg
VARIABLES hasLock, serverQueue, network, clientState
Client == 1..NumClients
Server == 0
Node == {Server} \cup Client
Message == [type : {LockMsg, UnlockMsg, GrantMsg}, from : Node]
Init == 
    /\ hasLock = [c \in Client |-> FALSE]
    /\ serverQueue = <<>>
    /\ network = [n \in Node |-> EmptyBag]
    /\ clientState = [c \in Client |-> "acquiring"]
vars == <<hasLock, serverQueue, network, clientState>>
ClientSendLock(c) == 
    /\ clientState[c] = "acquiring"
    /\ network' = [n \in Node |-> IF n = Server THEN network[n] \uplus {[type |-> LockMsg, from |-> c]} ELSE network[n]]
    /\ clientState' = [clientState EXCEPT ![c] = "waiting"]
    /\ UNCHANGED <<hasLock, serverQueue>>
ClientSendUnlock(c) == 
    /\ clientState[c] = "inCS"
    /\ hasLock[c] = TRUE
    /\ network' = [n \in Node |-> IF n = Server THEN network[n] \uplus {[type |-> UnlockMsg, from |-> c]} ELSE network[n]]
    /\ hasLock' = [hasLock EXCEPT ![c] = FALSE]
    /\ clientState' = [clientState EXCEPT ![c] = "acquiring"]
    /\ UNCHANGED serverQueue
ClientReceiveGrant(c) == 
    /\ \E m \in network[c] : m.type = GrantMsg
    /\ clientState[c] = "waiting"
    /\ LET chosen = CHOOSE m \in network[c] : m.type = GrantMsg IN
       network' = [n \in Node |-> IF n = c THEN network[n] \ {chosen} ELSE network[n]]
    /\ hasLock' = [hasLock EXCEPT ![c] = TRUE]
    /\ clientState' = [clientState EXCEPT ![c] = "inCS"]
    /\ UNCHANGED serverQueue
ServerProcessMessage == 
    /\ \E m \in network[Server] : TRUE
    /\ LET netServer = network[Server] IN
       LET msg = CHOOSE m \in netServer : TRUE IN
       LET newNetServer = netServer \ {msg} IN
       IF msg.type = LockMsg THEN
           LET c = msg.from IN
           IF Len(serverQueue) = 0 THEN
               /\ network' = [n \in Node |-> IF n = Server THEN newNetServer 
                                           ELSE IF n = c THEN network[n] \uplus {[type |-> GrantMsg, from |-> Server]}
                                           ELSE network[n]]
               /\ serverQueue' = Append(serverQueue, c)
           ELSE
               /\ network' = [n \in Node |-> IF n = Server THEN newNetServer ELSE network[n]]
               /\ serverQueue' = Append(serverQueue, c)
       ELSE
           /\ msg.type = UnlockMsg
           /\ Len(serverQueue) > 0
           /\ msg.from = Head(serverQueue)
           /\ LET newServerQueue = Tail(serverQueue) IN
              IF Len(newServerQueue) > 0 THEN
                 LET newHead = Head(newServerQueue) IN
                 /\ network' = [n \in Node |-> IF n = Server THEN newNetServer 
                                             ELSE IF n = newHead THEN network[n] \uplus {[type |-> GrantMsg, from |-> Server]}
                                             ELSE network[n]]
                 /\ serverQueue' = newServerQueue
              ELSE
                 /\ network' = [n \in Node |-> IF n = Server THEN newNetServer ELSE network[n]]
                 /\ serverQueue' = newServerQueue
    /\ UNCHANGED <<hasLock, clientState>>
Next == 
    \/ \E c \in Client : ClientSendLock(c)
    \/ \E c \in Client : ClientSendUnlock(c)
    \/ \E c \in Client : ClientReceiveGrant(c)
    \/ ServerProcessMessage
Spec == Init /\ [][Next]_vars /\ WF_vars(ServerProcessMessage) /\ WF_vars(\E c \in Client : ClientReceiveGrant(c)) /\ WF_vars(\E c \in Client : ClientSendLock(c)) /\ WF_vars(\E c \in Client : ClientSendUnlock(c))
====