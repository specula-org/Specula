---- MODULE locksvc ----
EXTENDS TLC, Sequences, Naturals, FiniteSets, Bags

CONSTANTS NumClients, Server

Client == 1..NumClients
Node == Client \cup {Server}

VARIABLES pc, network, q, hasLock

vars == <<pc, network, q, hasLock>>

Bag(S) == [S -> Nat]

TypeOK ==
    /\ pc \in [Node -> STRING]
    /\ network \in [Node -> Bag(UNION {[from: Client, type: {"Lock", "Unlock"}]} \cup {"Grant"})]
    /\ q \in Seq(Client)
    /\ hasLock \in [Client -> BOOLEAN]

Init ==
    /\ pc = [n \in Node |-> IF n \in Client THEN "acquireLock" ELSE "serverLoop"]
    /\ network = [n \in Node |-> EmptyBag]
    /\ q = <<>>
    /\ hasLock = [c \in Client |-> FALSE]

ClientRequestLock(c) ==
    /\ pc[c] = "acquireLock"
    /\ pc' = [pc EXCEPT ![c] = "criticalSection"]
    /\ LET msg == [from |-> c, type |-> "Lock"]
       IN network' = [network EXCEPT ![Server] = network[Server] \+ BagSingleton(msg)]
    /\ UNCHANGED <<q, hasLock>>

ClientEnterCS(c) ==
    /\ pc[c] = "criticalSection"
    /\ "Grant" \in BagToSet(network[c])
    /\ pc' = [pc EXCEPT ![c] = "unlock"]
    /\ hasLock' = [hasLock EXCEPT ![c] = TRUE]
    /\ network' = [network EXCEPT ![c] = network[c] -+ BagSingleton("Grant")]
    /\ UNCHANGED <<q>>

ClientUnlock(c) ==
    /\ pc[c] = "unlock"
    /\ pc' = [pc EXCEPT ![c] = "Done"]
    /\ hasLock' = [hasLock EXCEPT ![c] = FALSE]
    /\ LET msg == [from |-> c, type |-> "Unlock"]
       IN network' = [network EXCEPT ![Server] = network[Server] \+ BagSingleton(msg)]
    /\ UNCHANGED <<q>>

ServerProcessRequest ==
    /\ \E m \in BagToSet(network[Server]) : m.type = "Lock"
    /\ LET m == CHOOSE m_ \in BagToSet(network[Server]) : m_.type = "Lock"
       IN LET c == m.from
          IN LET new_q == Append(q, c)
             IN LET new_network_after_recv == [network EXCEPT ![Server] = network[Server] -+ BagSingleton(m)]
                IN /\ q' = new_q
                   /\ network' = IF Len(q) = 0
                                 THEN [new_network_after_recv EXCEPT ![c] = new_network_after_recv[c] \+ BagSingleton("Grant")]
                                 ELSE new_network_after_recv
                   /\ UNCHANGED <<pc, hasLock>>

ServerProcessUnlock ==
    /\ q /= <<>>
    /\ \E m \in BagToSet(network[Server]) :
        /\ m.type = "Unlock"
        /\ m.from = Head(q)
    /\ LET m == CHOOSE m_ \in BagToSet(network[Server]) :
                    /\ m_.type = "Unlock"
                    /\ m_.from = Head(q)
       IN LET new_q == Tail(q)
          IN LET new_network_after_recv == [network EXCEPT ![Server] = network[Server] -+ BagSingleton(m)]
             IN /\ q' = new_q
                /\ network' = IF new_q /= <<>>
                              THEN [new_network_after_recv EXCEPT ![Head(new_q)] = new_network_after_recv[Head(new_q)] \+ BagSingleton("Grant")]
                              ELSE new_network_after_recv
                /\ UNCHANGED <<pc, hasLock>>

Next ==
    \/ (\E c \in Client :
        \/ ClientRequestLock(c)
        \/ ClientEnterCS(c)
        \/ ClientUnlock(c))
    \/ ServerProcessRequest
    \/ ServerProcessUnlock

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

====