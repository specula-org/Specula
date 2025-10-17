---- MODULE etcdraft ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANT Producer, Consumers, Data, DefaultVal, DefaultConsumer

ASSUME IsFiniteSet(Consumers)
ASSUME Producer \notin Consumers
ASSUME IsFiniteSet(Data) /\ Cardinality(Data) > 0
ASSUME DefaultVal \notin Data
ASSUME DefaultConsumer \notin Consumers

Nodes == Consumers \cup {Producer}

RequestMsg(cons) == [type |-> "request", from |-> cons]
DataMsg(val, cons) == [type |-> "data", value |-> val, to |-> cons]

VARIABLES pc, queue, network, consumer_val, producer_val, producer_target

vars == <<pc, queue, network, consumer_val, producer_val, producer_target>>

Init ==
    /\ pc = [n \in Nodes |-> IF n \in Consumers THEN "c" ELSE "p"]
    /\ queue = <<>>
    /\ network = [n \in Nodes |-> <<>>]
    /\ consumer_val = [c \in Consumers |-> DefaultVal]
    /\ \E val \in Data : producer_val = val
    /\ producer_target = DefaultConsumer

ConsumerRequest(cons) ==
    /\ pc[cons] = "c"
    /\ pc' = [pc EXCEPT ![cons] = "c1"]
    /\ network' = [network EXCEPT ![Producer] = Append(@, RequestMsg(cons))]
    /\ UNCHANGED <<queue, consumer_val, producer_val, producer_target>>

ProducerReceiveRequest ==
    /\ pc[Producer] = "p"
    /\ network[Producer] /= <<>>
    /\ LET msg == Head(network[Producer]) IN
        /\ msg.type = "request"
        /\ pc' = [pc EXCEPT ![Producer] = "p1"]
        /\ network' = [network EXCEPT ![Producer] = Tail(@)]
        /\ producer_target' = msg.from
    /\ UNCHANGED <<queue, consumer_val, producer_val>>

ProducerProduce ==
    /\ pc[Producer] = "p1"
    /\ pc' = [pc EXCEPT ![Producer] = "p2"]
    /\ queue' = Append(queue, producer_val)
    /\ \E newVal \in Data : producer_val' = newVal
    /\ UNCHANGED <<network, consumer_val, producer_target>>

ProducerSend ==
    /\ pc[Producer] = "p2"
    /\ queue /= <<>>
    /\ producer_target \in Consumers
    /\ pc' = [pc EXCEPT ![Producer] = "p"]
    /\ LET dataToSend == Head(queue) IN
        /\ queue' = Tail(queue)
        /\ network' = [network EXCEPT ![producer_target] = Append(@, DataMsg(dataToSend, producer_target))]
    /\ producer_target' = DefaultConsumer
    /\ UNCHANGED <<consumer_val, producer_val>>

ConsumerReceive(cons) ==
    /\ pc[cons] = "c1"
    /\ network[cons] /= <<>>
    /\ LET msg == Head(network[cons]) IN
        /\ msg.type = "data"
        /\ msg.to = cons
        /\ pc' = [pc EXCEPT ![cons] = "c2"]
        /\ network' = [network EXCEPT ![cons] = Tail(@)]
        /\ consumer_val' = [consumer_val EXCEPT ![cons] = msg.value]
    /\ UNCHANGED <<queue, producer_val, producer_target>>

ConsumerReset(cons) ==
    /\ pc[cons] = "c2"
    /\ pc' = [pc EXCEPT ![cons] = "c"]
    /\ UNCHANGED <<queue, network, consumer_val, producer_val, producer_target>>

Next ==
    \/ (\E cons \in Consumers : ConsumerRequest(cons))
    \/ ProducerReceiveRequest
    \/ ProducerProduce
    \/ ProducerSend
    \/ (\E cons \in Consumers : ConsumerReceive(cons))
    \/ (\E cons \in Consumers : ConsumerReset(cons))

====