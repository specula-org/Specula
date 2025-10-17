---- MODULE etcdraft ----
EXTENDS TLC, Sequences, Naturals, FiniteSets

CONSTANT NumClients, Data

ASSUME IsFiniteSet(Data) /\ Data /= {}

Server == 0
ClientSet == 1..NumClients
NodeSet == {Server} \union ClientSet
Nil == "Nil"

VARIABLES
    client_state,
    server_q,
    dqueue,
    producer,
    network

vars == <<client_state, server_q, dqueue, producer, network>>

Init ==
    /\ client_state = [i \in ClientSet |-> "c"]
    /\ server_q = <<>>
    /\ dqueue = <<>>
    /\ producer = Nil
    /\ network = [n \in NodeSet |-> <<>>]

ClientRequest(i) ==
    /\ client_state[i] = "c"
    /\ client_state' = [client_state EXCEPT ![i] = "c1"]
    /\ network' = [network EXCEPT ![Server] = Append(@, [type |-> "request", from |-> i])]
    /\ UNCHANGED <<server_q, dqueue, producer>>

ClientBecomeProducer(i) ==
    /\ client_state[i] = "c1"
    /\ network[i] /= <<>>
    /\ Head(network[i]).type = "grant"
    /\ client_state' = [client_state EXCEPT ![i] = "p"]
    /\ network' = [network EXCEPT ![i] = Tail(@)]
    /\ UNCHANGED <<server_q, dqueue, producer>>

ClientProduce(i) ==
    /\ client_state[i] = "p"
    /\ \E d \in Data :
        /\ client_state' = [client_state EXCEPT ![i] = "p1"]
        /\ network' = [network EXCEPT ![Server] = Append(@, [type |-> "produce", from |-> i, data |-> d])]
    /\ UNCHANGED <<server_q, dqueue, producer>>

ClientFinishProduce(i) ==
    /\ client_state[i] = "p1"
    /\ client_state' = [client_state EXCEPT ![i] = "p2"]
    /\ network' = [network EXCEPT ![Server] = Append(@, [type |-> "release", from |-> i])]
    /\ UNCHANGED <<server_q, dqueue, producer>>

ClientBecomeConsumer(i) ==
    /\ client_state[i] = "p2"
    /\ client_state' = [client_state EXCEPT ![i] = "c2"]
    /\ UNCHANGED <<network, server_q, dqueue, producer>>

ClientReset(i) ==
    /\ client_state[i] = "c2"
    /\ client_state' = [client_state EXCEPT ![i] = "c"]
    /\ UNCHANGED <<network, server_q, dqueue, producer>>

ServerProcessRequest ==
    /\ network[Server] /= <<>>
    /\ Head(network[Server]).type = "request"
    /\ LET msg == Head(network[Server]) IN
        /\ server_q' = Append(server_q, msg.from)
        /\ network' = [network EXCEPT ![Server] = Tail(@)]
    /\ UNCHANGED <<client_state, dqueue, producer>>

ServerGrant ==
    /\ producer = Nil
    /\ Len(server_q) > 0
    /\ LET i == Head(server_q) IN
        /\ producer' = i
        /\ server_q' = server_q
        /\ network' = [network EXCEPT ![i] = Append(@, [type |-> "grant"])]
    /\ UNCHANGED <<client_state, dqueue>>

ServerEnqueue ==
    /\ network[Server] /= <<>>
    /\ Head(network[Server]).type = "produce"
    /\ LET msg == Head(network[Server]) IN
        /\ dqueue' = Append(dqueue, msg.data)
        /\ network' = [network EXCEPT ![Server] = Tail(@)]
    /\ UNCHANGED <<client_state, server_q, producer>>

ServerProcessRelease ==
    /\ network[Server] /= <<>>
    /\ LET msg == Head(network[Server]) IN
        /\ msg.type = "release"
        /\ msg.from = producer
        /\ Len(server_q) > 0
        /\ Head(server_q) = msg.from
        /\ server_q' = Tail(server_q)
        /\ producer' = Nil
        /\ network' = [network EXCEPT ![Server] = Tail(@)]
    /\ UNCHANGED <<client_state, dqueue>>

Next ==
    \/ \E i \in ClientSet :
        \/ ClientRequest(i)
        \/ ClientBecomeProducer(i)
        \/ ClientProduce(i)
        \/ ClientFinishProduce(i)
        \/ ClientBecomeConsumer(i)
        \/ ClientReset(i)
    \/ ServerProcessRequest
    \/ ServerGrant
    \/ ServerEnqueue
    \/ ServerProcessRelease

Spec == Init /\ [][Next]_vars

====