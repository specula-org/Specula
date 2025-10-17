---- MODULE etcdraft ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS
    Producer,
    Consumers,
    Data

ASSUME
    /\ Producer \notin Consumers
    /\ IsFiniteSet(Consumers)
    /\ Consumers /= {}
    /\ IsFiniteSet(Data)
    /\ Data /= {}

Nodes == {Producer} \cup Consumers
Nil == CHOOSE v : v \notin Data

VARIABLES
    pc,
    queue,
    network,
    consumer_val

vars == <<pc, queue, network, consumer_val>>

Message == [type: {"request", "produce"}, from: Nodes, value: Data \cup {Nil}]

TypeOK ==
    /\ \A n \in Nodes :
        IF n = Producer THEN pc[n] \in {"p", "p1", "p2"}
        ELSE pc[n] \in {"c", "c1", "c2"}
    /\ queue \in Seq(Data)
    /\ network \in [Nodes -> Seq(Message)]
    /\ consumer_val \in [Consumers -> Data \cup {Nil}]

Init ==
    /\ pc = [n \in Nodes |-> IF n = Producer THEN "p" ELSE "c"]
    /\ queue = <<>>
    /\ network = [n \in Nodes |-> <<>>]
    /\ consumer_val = [c \in Consumers |-> Nil]

P_Produce ==
    /\ pc[Producer] = "p"
    /\ \E d \in Data:
        /\ queue' = Append(queue, d)
        /\ pc' = [pc EXCEPT ![Producer] = "p1"]
    /\ UNCHANGED <<network, consumer_val>>

P_Transition1 ==
    /\ pc[Producer] = "p1"
    /\ pc' = [pc EXCEPT ![Producer] = "p2"]
    /\ UNCHANGED <<queue, network, consumer_val>>

P_Transition2 ==
    /\ pc[Producer] = "p2"
    /\ pc' = [pc EXCEPT ![Producer] = "p"]
    /\ UNCHANGED <<queue, network, consumer_val>>

P_ServeRequest ==
    /\ Len(network[Producer]) > 0
    /\ LET msg == Head(network[Producer]) IN
        /\ msg.type = "request"
        /\ Len(queue) > 0
        /\ LET dataToSend == Head(queue)
               responseMsg == [type |-> "produce", value |-> dataToSend, from |-> Producer]
           IN
            /\ queue' = Tail(queue)
            /\ network' = [network EXCEPT ![Producer] = Tail(@),
                                         ![msg.from] = Append(@, responseMsg)]
    /\ UNCHANGED <<pc, consumer_val>>

C_Request(self) ==
    /\ self \in Consumers
    /\ pc[self] = "c"
    /\ LET requestMsg == [type |-> "request", from |-> self, value |-> Nil] IN
        /\ network' = [network EXCEPT ![Producer] = Append(@, requestMsg)]
    /\ pc' = [pc EXCEPT ![self] = "c1"]
    /\ UNCHANGED <<queue, consumer_val>>

C_Receive(self) ==
    /\ self \in Consumers
    /\ pc[self] = "c1"
    /\ Len(network[self]) > 0
    /\ LET msg == Head(network[self]) IN
        /\ msg.type = "produce"
        /\ network' = [network EXCEPT ![self] = Tail(@)]
        /\ consumer_val' = [consumer_val EXCEPT ![self] = msg.value]
        /\ pc' = [pc EXCEPT ![self] = "c2"]
    /\ UNCHANGED <<queue>>

C_Finish(self) ==
    /\ self \in Consumers
    /\ pc[self] = "c2"
    /\ pc' = [pc EXCEPT ![self] = "c"]
    /\ consumer_val' = [consumer_val EXCEPT ![self] = Nil]
    /\ UNCHANGED <<queue, network>>

Next ==
    \/ P_Produce
    \/ P_Transition1
    \/ P_Transition2
    \/ P_ServeRequest
    \/ \E self \in Consumers : C_Request(self)
    \/ \E self \in Consumers : C_Receive(self)
    \/ \E self \in Consumers : C_Finish(self)

Spec == Init /\ [][Next]_vars

====