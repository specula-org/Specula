---- MODULE etcdraft ----
EXTENDS TLC, Sequences, Naturals, FiniteSets

CONSTANTS
    Producer,
    Consumers,
    Data,
    Nil

ASSUME
    /\ Producer \notin Consumers
    /\ IsFiniteSet(Consumers)
    /\ Cardinality(Consumers) >= 1
    /\ IsFiniteSet(Data)
    /\ Cardinality(Data) >= 1

VARIABLES
    pc,
    network,
    currentRequester,
    producedData

vars == <<pc, network, currentRequester, producedData>>

Nodes == {Producer} \cup Consumers
ProducerStates == {"p", "p1", "p2"}
ConsumerStates == {"c", "c1", "c2"}

Init ==
    /\ pc = [n \in Nodes |-> IF n = Producer THEN "p" ELSE "c"]
    /\ network = [n \in Nodes |-> <<>>]
    /\ currentRequester = Nil
    /\ producedData = Nil

P_ReceiveRequest ==
    /\ pc[Producer] = "p"
    /\ currentRequester = Nil
    /\ network[Producer] /= <<>>
    /\ LET msg == Head(network[Producer]) IN
        /\ msg.type = "request"
        /\ msg.from \in Consumers
        /\ pc' = [pc EXCEPT ![Producer] = "p1"]
        /\ network' = [network EXCEPT ![Producer] = Tail(network[Producer])]
        /\ currentRequester' = msg.from
        /\ UNCHANGED producedData

P_ProduceData ==
    /\ pc[Producer] = "p1"
    /\ \E d \in Data:
        /\ pc' = [pc EXCEPT ![Producer] = "p2"]
        /\ producedData' = d
        /\ UNCHANGED <<network, currentRequester>>

P_SendData ==
    /\ pc[Producer] = "p2"
    /\ currentRequester \in Consumers
    /\ LET dest == currentRequester
           msg == [type |-> "produce", to |-> dest, data |-> producedData]
    IN
        /\ pc' = [pc EXCEPT ![Producer] = "p"]
        /\ network' = [network EXCEPT ![dest] = Append(network[dest], msg)]
        /\ currentRequester' = Nil
        /\ producedData' = Nil

C_SendRequest(c) ==
    /\ c \in Consumers
    /\ pc[c] = "c"
    /\ LET msg == [type |-> "request", from |-> c] IN
        /\ pc' = [pc EXCEPT ![c] = "c1"]
        /\ network' = [network EXCEPT ![Producer] = Append(network[Producer], msg)]
        /\ UNCHANGED <<currentRequester, producedData>>

C_ReceiveData(c) ==
    /\ c \in Consumers
    /\ pc[c] = "c1"
    /\ network[c] /= <<>>
    /\ LET msg == Head(network[c]) IN
        /\ msg.type = "produce"
        /\ pc' = [pc EXCEPT ![c] = "c2"]
        /\ network' = [network EXCEPT ![c] = Tail(network[c])]
        /\ UNCHANGED <<currentRequester, producedData>>

C_ConsumeData(c) ==
    /\ c \in Consumers
    /\ pc[c] = "c2"
    /\ pc' = [pc EXCEPT ![c] = "c"]
    /\ UNCHANGED <<network, currentRequester, producedData>>

Next ==
    \/ P_ReceiveRequest
    \/ P_ProduceData
    \/ P_SendData
    \/ \E c \in Consumers: C_SendRequest(c)
    \/ \E c \in Consumers: C_ReceiveData(c)
    \/ \E c \in Consumers: C_ConsumeData(c)

Spec == Init /\ [][Next]_vars

=============================================================================