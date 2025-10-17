---- MODULE etcdraft ----
EXTENDS Sequences, Naturals, FiniteSets

CONSTANT NumClients

VARIABLES
    network,
    serverQueue,
    clientState,
    serverState

Nodes == 0..NumClients
Server == 0
Clients == 1..NumClients

MessageType == {"request", "produce"}

Message == [type : MessageType, from : Nodes, to : Nodes]

Vars == <<network, serverQueue, clientState, serverState>>

Init ==
    /\ network = [n \in Nodes |-> <<>>]
    /\ serverQueue = <<>>
    /\ clientState = [c \in Clients |-> "c"]
    /\ serverState = "p"

ClientSendRequest(c) ==
    /\ clientState[c] = "c"
    /\ LET msg == [type |-> "request", from |-> c, to |-> Server]
       IN network' = [network EXCEPT ![Server] = Append(@, msg)]
    /\ clientState' = [clientState EXCEPT ![c] = "c1"]
    /\ UNCHANGED <<serverQueue, serverState>>

ServerReceiveRequest ==
    /\ serverState = "p"
    /\ Len(network[Server]) > 0
    /\ LET msg == Head(network[Server])
       IN /\ msg.type = "request"
          /\ serverQueue' = Append(serverQueue, msg.from)
          /\ network' = [network EXCEPT ![Server] = Tail(@)]
          /\ serverState' = "p1"
    /\ UNCHANGED clientState

ServerProduce ==
    /\ serverState = "p1"
    /\ serverQueue /= <<>>
    /\ serverState' = "p2"
    /\ UNCHANGED <<network, serverQueue, clientState>>

ServerSendProduce ==
    /\ serverState = "p2"
    /\ serverQueue /= <<>>
    /\ LET consumer == Head(serverQueue)
           msg == [type |-> "produce", from |-> Server, to |-> consumer]
       IN /\ network' = [network EXCEPT ![consumer] = Append(@, msg)]
          /\ serverQueue' = Tail(serverQueue)
          /\ serverState' = IF serverQueue' = <<>> THEN "p" ELSE "p1"
    /\ UNCHANGED clientState

ClientReceiveProduce(c) ==
    /\ clientState[c] = "c1"
    /\ Len(network[c]) > 0
    /\ LET msg == Head(network[c])
       IN /\ msg.type = "produce"
          /\ network' = [network EXCEPT ![c] = Tail(@)]
          /\ clientState' = [clientState EXCEPT ![c] = "c2"]
    /\ UNCHANGED <<serverQueue, serverState>>

ClientReset(c) ==
    /\ clientState[c] = "c2"
    /\ clientState' = [clientState EXCEPT ![c] = "c"]
    /\ UNCHANGED <<network, serverQueue, serverState>>

Next ==
    \/ \E c \in Clients : ClientSendRequest(c)
    \/ ServerReceiveRequest
    \/ ServerProduce
    \/ ServerSendProduce
    \/ \E c \in Clients : ClientReceiveProduce(c)
    \/ \E c \in Clients : ClientReset(c)

Spec == Init /\ [][Next]_Vars

====