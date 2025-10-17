---- MODULE etcdraft ----
EXTENDS TLC, Sequences, Naturals, FiniteSets

CONSTANTS NumClients, ServerID
ASSUME ServerID = 0
Node == {ServerID} \union (1..NumClients)

VARIABLES 
    serverQueue,
    network,
    clientState,
    producerState

vars == <<serverQueue, network, clientState, producerState>>

Init ==
    /\ serverQueue = <<>>
    /\ network = [n \in Node |-> {}]
    /\ clientState = [c \in 1..NumClients |-> "c"]
    /\ producerState = "p"

ServerReceiveLock(c) ==
    /\ serverQueue' = Append(serverQueue, c)
    /\ IF Len(serverQueue) = 0
       THEN /\ network' = [network EXCEPT ![c] = @ \union {[type |-> "GrantMsg"]}]
       ELSE /\ UNCHANGED network
    /\ UNCHANGED <<clientState, producerState>>

ServerReceiveUnlock ==
    /\ serverQueue' = Tail(serverQueue)
    /\ IF Len(serverQueue') > 0
       THEN LET head == Head(serverQueue') IN
            network' = [network EXCEPT ![head] = @ \union {[type |-> "GrantMsg"]}]
       ELSE /\ network' = network
    /\ UNCHANGED <<clientState, producerState>>

ClientSendLock(c) ==
    /\ clientState[c] = "c"
    /\ network' = [network EXCEPT ![ServerID] = @ \union {[type |-> "LockMsg", from |-> c]}]
    /\ clientState' = [clientState EXCEPT ![c] = "c1"]
    /\ UNCHANGED <<serverQueue, producerState>>

ClientReceiveGrant(c) ==
    \E msg \in network[c]:
        /\ msg.type = "GrantMsg"
        /\ clientState' = [clientState EXCEPT ![c] = "c2"]
        /\ network' = [network EXCEPT ![c] = @ \ {msg}]
        /\ UNCHANGED <<serverQueue, producerState>>

ClientSendUnlock(c) ==
    /\ clientState[c] = "c2"
    /\ network' = [network EXCEPT ![ServerID] = @ \union {[type |-> "UnlockMsg", from |-> c]}]
    /\ clientState' = [clientState EXCEPT ![c] = "c"]
    /\ UNCHANGED <<serverQueue, producerState>>

ProducerSendProduce ==
    /\ producerState = "p"
    /\ network' = [network EXCEPT ![ServerID] = @ \union {[type |-> "ProduceMsg"]}]
    /\ producerState' = "p1"
    /\ UNCHANGED <<serverQueue, clientState>>

ProducerReceiveAck ==
    \E msg \in network[ServerID]:
        /\ msg.type = "AckMsg"
        /\ producerState' = "p2"
        /\ network' = [network EXCEPT ![ServerID] = @ \ {msg}]
        /\ UNCHANGED <<serverQueue, clientState>>

Next ==
    \/ \E c \in 1..NumClients: ClientSendLock(c)
    \/ \E c \in 1..NumClients: ClientReceiveGrant(c)
    \/ \E c \in 1..NumClients: ClientSendUnlock(c)
    \/ \E msg \in network[ServerID]:
        \/ (msg.type = "LockMsg") /\ ServerReceiveLock(msg.from)
        \/ (msg.type = "UnlockMsg") /\ ServerReceiveUnlock
    \/ ProducerSendProduce
    \/ ProducerReceiveAck

Spec == Init /\ [][Next]_vars
====