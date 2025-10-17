---- MODULE etcdraft ----

EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS NumClients

VARIABLES network, hasLock, serverQueue, pc

vars == <<network, hasLock, serverQueue, pc>>

ServerID == 0
ClientSet == 1..NumClients
NodeSet == {ServerID} \cup ClientSet

RequestMsg == 1
ProduceMsg == 2
GrantMsg == 3

Message == [from: NodeSet, type: {RequestMsg, ProduceMsg, GrantMsg}]

TypeOK == 
    /\ network \in [NodeSet -> Seq(Message \cup {GrantMsg})]
    /\ hasLock \in [ClientSet -> BOOLEAN]
    /\ serverQueue \in Seq(ClientSet)
    /\ pc \in [NodeSet -> {"c", "c1", "c2", "p", "p1", "p2", "serverLoop", "serverReceive", "serverRespond", "Done"}]

Init ==
    /\ network = [n \in NodeSet |-> <<>>]
    /\ hasLock = [c \in ClientSet |-> FALSE]
    /\ serverQueue = <<>>
    /\ pc = [n \in NodeSet |-> IF n = ServerID THEN "serverLoop" ELSE "c"]

ServerLoop ==
    /\ pc[ServerID] = "serverLoop"
    /\ pc' = [pc EXCEPT ![ServerID] = "serverReceive"]
    /\ UNCHANGED <<network, hasLock, serverQueue>>

ServerReceive ==
    /\ pc[ServerID] = "serverReceive"
    /\ Len(network[ServerID]) > 0
    /\ pc' = [pc EXCEPT ![ServerID] = "serverRespond"]
    /\ UNCHANGED <<network, hasLock, serverQueue>>

ServerRespond ==
    /\ pc[ServerID] = "serverRespond"
    /\ Len(network[ServerID]) > 0
    /\ LET msg == Head(network[ServerID])
       IN /\ LET newNetwork == [network EXCEPT ![ServerID] = Tail(@)]
             IN /\ IF msg.type = RequestMsg
                   THEN /\ IF serverQueue = <<>>
                           THEN network' = [newNetwork EXCEPT ![msg.from] = Append(@, GrantMsg)]
                           ELSE network' = newNetwork
                        /\ serverQueue' = Append(serverQueue, msg.from)
                        /\ UNCHANGED hasLock
                   ELSE IF msg.type = ProduceMsg
                        THEN /\ serverQueue' = Tail(serverQueue)
                             /\ IF serverQueue' /= <<>>
                                THEN network' = [newNetwork EXCEPT ![Head(serverQueue')] = Append(@, GrantMsg)]
                                ELSE network' = newNetwork
                             /\ UNCHANGED hasLock
                        ELSE /\ network' = newNetwork
                             /\ UNCHANGED <<serverQueue, hasLock>>
          /\ pc' = [pc EXCEPT ![ServerID] = "serverLoop"]

ClientStateC(c) ==
    /\ pc[c] = "c"
    /\ network' = [network EXCEPT ![ServerID] = Append(@, [from |-> c, type |-> RequestMsg])]
    /\ pc' = [pc EXCEPT ![c] = "c1"]
    /\ UNCHANGED <<hasLock, serverQueue>>

ClientStateC1(c) ==
    /\ pc[c] = "c1"
    /\ Len(network[c]) > 0
    /\ Head(network[c]) = GrantMsg
    /\ network' = [network EXCEPT ![c] = Tail(@)]
    /\ hasLock' = [hasLock EXCEPT ![c] = TRUE]
    /\ pc' = [pc EXCEPT ![c] = "p"]
    /\ UNCHANGED serverQueue

ClientStateP(c) ==
    /\ pc[c] = "p"
    /\ pc' = [pc EXCEPT ![c] = "p1"]
    /\ UNCHANGED <<network, hasLock, serverQueue>>

ClientStateP1(c) ==
    /\ pc[c] = "p1"
    /\ pc' = [pc EXCEPT ![c] = "p2"]
    /\ UNCHANGED <<network, hasLock, serverQueue>>

ClientStateP2(c) ==
    /\ pc[c] = "p2"
    /\ hasLock' = [hasLock EXCEPT ![c] = FALSE]
    /\ network' = [network EXCEPT ![ServerID] = Append(@, [from |-> c, type |-> ProduceMsg])]
    /\ pc' = [pc EXCEPT ![c] = "c2"]
    /\ UNCHANGED serverQueue

ClientStateC2(c) ==
    /\ pc[c] = "c2"
    /\ pc' = [pc EXCEPT ![c] = "Done"]
    /\ UNCHANGED <<network, hasLock, serverQueue>>

Next ==
    \/ ServerLoop
    \/ ServerReceive  
    \/ ServerRespond
    \/ \E c \in ClientSet:
        \/ ClientStateC(c)
        \/ ClientStateC1(c)
        \/ ClientStateP(c)
        \/ ClientStateP1(c)
        \/ ClientStateP2(c)
        \/ ClientStateC2(c)

Spec == Init /\ [][Next]_vars

====