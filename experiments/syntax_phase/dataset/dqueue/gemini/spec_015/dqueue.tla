---- MODULE etcdraft ----
EXTENDS TLC, Sequences, Naturals, FiniteSets

CONSTANTS Producer, Consumers, Data

ASSUME Producer \notin Consumers
ASSUME IsFiniteSet(Consumers)
ASSUME Cardinality(Consumers) >= 1
ASSUME IsFiniteSet(Data)
ASSUME Cardinality(Data) >= 1

Nil == CHOOSE v : v \notin Data

Nodes == {Producer} \cup Consumers
MsgType == {"request", "produce"}

VARIABLES pc, network, queue, produced_data, consumed_data

vars == <<pc, network, queue, produced_data, consumed_data>>

Init ==
    /\ pc = [n \in Nodes |-> IF n = Producer THEN "p" ELSE "c"]
    /\ network = <<>>
    /\ queue = <<>>
    /\ produced_data = Nil
    /\ consumed_data = [c \in Consumers |-> Nil]

C_Request(self) ==
    /\ self \in Consumers
    /\ pc[self] = "c"
    /\ pc' = [pc EXCEPT ![self] = "c1"]
    /\ network' = Append(network, [type |-> "request", from |-> self, to |-> Producer])
    /\ UNCHANGED <<queue, produced_data, consumed_data>>

C_Receive(self) ==
    /\ self \in Consumers
    /\ pc[self] = "c1"
    /\ network /= <<>>
    /\ LET msg == Head(network) IN
        /\ msg.to = self
        /\ msg.type = "produce"
        /\ pc' = [pc EXCEPT ![self] = "c2"]
        /\ network' = Tail(network)
        /\ consumed_data' = [consumed_data EXCEPT ![self] = msg.payload]
        /\ UNCHANGED <<queue, produced_data>>

P_ReceiveRequest ==
    /\ pc[Producer] = "p"
    /\ network /= <<>>
    /\ LET msg == Head(network) IN
        /\ msg.to = Producer
        /\ msg.type = "request"
        /\ pc' = [pc EXCEPT ![Producer] = "p1"]
        /\ network' = Tail(network)
        /\ queue' = Append(queue, msg.from)
        /\ UNCHANGED <<produced_data, consumed_data>>

P_Produce ==
    /\ pc[Producer] = "p1"
    /\ queue /= <<>>
    /\ pc' = [pc EXCEPT ![Producer] = "p2"]
    /\ \E d \in Data : produced_data' = d
    /\ UNCHANGED <<network, queue, consumed_data>>

P_Send ==
    /\ pc[Producer] = "p2"
    /\ queue /= <<>>
    /\ LET recipient == Head(queue) IN
        /\ pc' = [pc EXCEPT ![Producer] = "p"]
        /\ network' = Append(network, [type |-> "produce", from |-> Producer, to |-> recipient, payload |-> produced_data])
        /\ queue' = Tail(queue)
        /\ produced_data' = Nil
        /\ UNCHANGED <<consumed_data>>

Next ==
    \/ (\E self \in Consumers : C_Request(self) \/ C_Receive(self))
    \/ P_ReceiveRequest
    \/ P_Produce
    \/ P_Send

Spec == Init /\ [][Next]_vars

=============================================================================