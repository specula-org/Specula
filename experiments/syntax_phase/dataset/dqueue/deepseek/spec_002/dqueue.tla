---- MODULE etcdraft ----
EXTENDS Sequences, Integers, FiniteSets

CONSTANTS NumConsumers, NULL

VARIABLES consumerState, producerState, network, currentConsumer

Nodes == 0..NumConsumers
Producer == 0
Consumers == 1..NumConsumers

MessageType == {"request", "produce"}

Message == [type : MessageType, from : Nodes, to : Nodes]

Init ==
    /\ producerState = [node |-> Producer, state |-> "p"]
    /\ consumerState = [c \in Consumers |-> "c"]
    /\ network = <<>>
    /\ currentConsumer = NULL

ProducerSendRequest ==
    /\ producerState.state = "p"
    /\ \E c \in Consumers:
        /\ consumerState[c] = "c"
        /\ network' = Append(network, [type |-> "request", from |-> Producer, to |-> c])
        /\ producerState' = [producerState EXCEPT !.state = "p1"]
        /\ consumerState' = [consumerState EXCEPT ![c] = "c1"]
        /\ currentConsumer' = c
    /\ UNCHANGED <<>>

ProducerSendProduce ==
    /\ producerState.state = "p1"
    /\ network' = Append(network, [type |-> "produce", from |-> Producer, to |-> currentConsumer])
    /\ producerState' = [producerState EXCEPT !.state = "p2"]
    /\ UNCHANGED <<consumerState, currentConsumer>>

ProducerComplete ==
    /\ producerState.state = "p2"
    /\ producerState' = [producerState EXCEPT !.state = "p"]
    /\ currentConsumer' = NULL
    /\ UNCHANGED <<consumerState, network>>

ConsumerReceive ==
    /\ \E msg \in 1..Len(network):
        /\ consumerState[network[msg].to] = "c1"
        /\ network[msg].type = "produce"
        /\ consumerState' = [consumerState EXCEPT ![network[msg].to] = "c2"]
        /\ network' = [i \in 1..(Len(network)-1) |-> 
                         IF i < msg THEN network[i] ELSE network[i+1]]
    /\ UNCHANGED <<producerState, currentConsumer>>

ConsumerProcess ==
    /\ \E c \in Consumers:
        /\ consumerState[c] = "c2"
        /\ consumerState' = [consumerState EXCEPT ![c] = "c"]
    /\ UNCHANGED <<producerState, network, currentConsumer>>

Next ==
    \/ ProducerSendRequest
    \/ ProducerSendProduce
    \/ ProducerComplete
    \/ ConsumerReceive
    \/ ConsumerProcess

Spec == Init /\ [][Next]_<<consumerState, producerState, network, currentConsumer>>

====