---- MODULE etcdraft ----
EXTENDS Sequences, Naturals, FiniteSets

CONSTANTS NumClients

VARIABLES
    consumerState,
    producerState,
    queue,
    network

vars == <<consumerState, producerState, queue, network>>

NodeSet == 0..NumClients
ProducerID == 0
ConsumerSet == 1..NumClients

Init ==
    /\ producerState = "p"
    /\ consumerState = [i \in ConsumerSet |-> "c"]
    /\ queue = <<>>
    /\ network = <<>>

SendRequest(i) ==
    /\ consumerState[i] = "c"
    /\ consumerState' = [consumerState EXCEPT ![i] = "c1"]
    /\ network' = Append(network, [type |-> "request", from |-> i, to |-> ProducerID])
    /\ UNCHANGED <<producerState, queue>>

ReceiveRequest ==
    /\ \E msg \in DOMAIN network :
        /\ network[msg].to = ProducerID
        /\ network[msg].type = "request"
        /\ LET i == network[msg].from IN
            /\ queue' = Append(queue, i)
            /\ network' = [j \in 1..(Len(network)-1) |->
                IF j < msg THEN network[j] ELSE network[j+1]]
            /\ IF Len(queue) = 1 THEN producerState' = "p1" ELSE UNCHANGED producerState
    /\ UNCHANGED consumerState

ProduceStep ==
    /\ producerState = "p1"
    /\ producerState' = "p2"
    /\ UNCHANGED <<consumerState, queue, network>>

SendProduce ==
    /\ producerState = "p2"
    /\ queue /= <<>>
    /\ LET nextConsumer == Head(queue) IN
        /\ network' = Append(network, [type |-> "produce", from |-> ProducerID, to |-> nextConsumer])
        /\ queue' = Tail(queue)
        /\ producerState' = IF queue' = <<>> THEN "p" ELSE "p1"
    /\ UNCHANGED consumerState

ReceiveProduce(i) ==
    /\ \E msg \in DOMAIN network :
        /\ network[msg].to = i
        /\ network[msg].type = "produce"
        /\ consumerState[i] = "c1"
        /\ consumerState' = [consumerState EXCEPT ![i] = "c2"]
        /\ network' = [j \in 1..(Len(network)-1) |->
            IF j < msg THEN network[j] ELSE network[j+1]]
    /\ UNCHANGED <<producerState, queue>>

Consume(i) ==
    /\ consumerState[i] = "c2"
    /\ consumerState' = [consumerState EXCEPT ![i] = "c"]
    /\ UNCHANGED <<producerState, queue, network>>

Next ==
    \/ \E i \in ConsumerSet: SendRequest(i)
    \/ ReceiveRequest
    \/ ProduceStep
    \/ SendProduce
    \/ \E i \in ConsumerSet: ReceiveProduce(i)
    \/ \E i \in ConsumerSet: Consume(i)

Spec == Init /\ [][Next]_vars

====