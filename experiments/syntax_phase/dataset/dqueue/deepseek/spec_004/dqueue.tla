---- MODULE dqueue ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS NumClients

VARIABLES consumerState, producerState, pending, net, currentConsumer

Nodes == 0..NumClients
Producer == 0
Consumers == 1..NumClients
MessageType == {"request", "produce"}

Init ==
    /\ consumerState = [c \in Consumers |-> "c"]
    /\ producerState = "p"
    /\ pending = <<>>
    /\ net = <<>>
    /\ currentConsumer = 0

Send(c) ==
    /\ consumerState[c] = "c"
    /\ net' = Append(net, [type |-> "request", from |-> c, to |-> Producer])
    /\ consumerState' = [consumerState EXCEPT ![c] = "c1"]
    /\ UNCHANGED <<producerState, pending, currentConsumer>>

RecvReq ==
    /\ Len(net) > 0
    /\ Head(net).type = "request"
    /\ Head(net).to = Producer
    /\ pending' = Append(pending, Head(net).from)
    /\ net' = Tail(net)
    /\ UNCHANGED <<consumerState, producerState, currentConsumer>>

StartProduce ==
    /\ producerState = "p"
    /\ Len(pending) > 0
    /\ currentConsumer' = Head(pending)
    /\ producerState' = "p1"
    /\ pending' = Tail(pending)
    /\ UNCHANGED <<consumerState, net>>

SendProduce ==
    /\ producerState = "p1"
    /\ net' = Append(net, [type |-> "produce", from |-> Producer, to |-> currentConsumer])
    /\ producerState' = "p2"
    /\ UNCHANGED <<consumerState, pending, currentConsumer>>

FinishProduce ==
    /\ producerState = "p2"
    /\ producerState' = "p"
    /\ currentConsumer' = 0
    /\ UNCHANGED <<consumerState, pending, net>>

RecvProduce ==
    /\ Len(net) > 0
    /\ Head(net).type = "produce"
    /\ Head(net).to \in Consumers
    /\ consumerState[Head(net).to] = "c1"
    /\ consumerState' = [consumerState EXCEPT ![Head(net).to] = "c2"]
    /\ net' = Tail(net)
    /\ UNCHANGED <<producerState, pending, currentConsumer>>

Consume ==
    /\ \E c \in Consumers: consumerState[c] = "c2"
    /\ consumerState' = [consumerState EXCEPT ![c] = "c"]
    /\ UNCHANGED <<producerState, pending, net, currentConsumer>>

Next ==
    \/ \E c \in Consumers: Send(c)
    \/ RecvReq
    \/ StartProduce
    \/ SendProduce
    \/ FinishProduce
    \/ RecvProduce
    \/ Consume

Spec == Init /\ [][Next]_<<consumerState, producerState, pending, net, currentConsumer>>
====