---- MODULE etcdraft ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Producer, Consumers

ASSUME IsFiniteSet(Consumers) /\ (Producer \notin Consumers)

Nodes == Consumers \cup {Producer}
Nil == CHOOSE x: x = x

VARIABLES node_state, network, producer_requester

vars == <<node_state, network, producer_requester>>

PStates == {"p", "p1", "p2"}
CStates == {"c", "c1", "c2"}

Init ==
    /\ node_state = [n \in Nodes |-> IF n = Producer THEN "p" ELSE "c"]
    /\ network = EmptyBag
    /\ producer_requester = Nil

ConsumerRequest(cons) ==
    /\ cons \in Consumers
    /\ node_state[cons] = "c"
    /\ node_state' = [node_state EXCEPT ![cons] = "c1"]
    /\ LET msg == [type |-> "request", from |-> cons]
       IN network' = network (+) <<msg>>
    /\ UNCHANGED <<producer_requester>>

ProducerProcessRequest ==
    /\ node_state[Producer] = "p"
    /\ \E msg \in BagToSet(network) : msg.type = "request"
    /\ LET RequestMsgs == {m \in BagToSet(network) : m.type = "request"}
       IN \E msg \in RequestMsgs :
            /\ network' = network (-) <<msg>>
            /\ node_state' = [node_state EXCEPT ![Producer] = "p1"]
            /\ producer_requester' = msg.from

ProducerSend ==
    /\ node_state[Producer] = "p1"
    /\ node_state' = [node_state EXCEPT ![Producer] = "p2"]
    /\ LET msg == [type |-> "produce", to |-> producer_requester]
       IN network' = network (+) <<msg>>
    /\ UNCHANGED <<producer_requester>>

ProducerReset ==
    /\ node_state[Producer] = "p2"
    /\ node_state' = [node_state EXCEPT ![Producer] = "p"]
    /\ producer_requester' = Nil
    /\ UNCHANGED <<network>>

ConsumerReceive(cons) ==
    /\ cons \in Consumers
    /\ node_state[cons] = "c1"
    /\ \E msg \in BagToSet(network) : msg.type = "produce" /\ msg.to = cons
    /\ LET ResponseMsgs == {m \in BagToSet(network) : m.type = "produce" /\ m.to = cons}
       IN \E msg \in ResponseMsgs :
            /\ network' = network (-) <<msg>>
            /\ node_state' = [node_state EXCEPT ![cons] = "c2"]
    /\ UNCHANGED <<producer_requester>>

ConsumerReset(cons) ==
    /\ cons \in Consumers
    /\ node_state[cons] = "c2"
    /\ node_state' = [node_state EXCEPT ![cons] = "c"]
    /\ UNCHANGED <<network, producer_requester>>

Next ==
    \/ \E cons \in Consumers : ConsumerRequest(cons)
    \/ ProducerProcessRequest
    \/ ProducerSend
    \/ ProducerReset
    \/ \E cons \in Consumers : ConsumerReceive(cons)
    \/ \E cons \in Consumers : ConsumerReset(cons)

====