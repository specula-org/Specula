---- MODULE locksvc ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS NumClients

ASSUME NumClients \in Nat \ {0}

Server == 0
Client == 1..NumClients
Node == {Server} \cup Client

RequestMsg == [type: {"Lock", "Unlock"}, from: Client]
GrantMsgValue == "Grant"
Message == RequestMsg \cup {GrantMsgValue}

VARIABLES pc, q, hasLock, network

vars == <<pc, q, hasLock, network>>

ClientLabels == {"acquireLock", "criticalSection", "unlock", "Done"}
ServerLabels == {"serverLoop"}

TypeOK ==
    /\ pc \in [Node -> ClientLabels \cup ServerLabels]
    /\ q \in Seq(Client)
    /\ hasLock \in [Client -> BOOLEAN]
    /\ network \in [Node -> Bags(Message)]

Init ==
    /\ pc = [n \in Node |-> IF n = Server THEN "serverLoop" ELSE "acquireLock"]
    /\ q = <<>>
    /\ hasLock = [c \in Client |-> FALSE]
    /\ network = [n \in Node |-> EmptyBag]

ClientAcquireLock(c) ==
    /\ pc[c] = "acquireLock"
    /\ LET msg == [type |-> "Lock", from |-> c] IN
       network' = [network EXCEPT ![Server] = network[Server] \cup Bag({msg})]
    /\ pc' = [pc EXCEPT ![c] = "criticalSection"]
    /\ UNCHANGED <<q, hasLock>>

ClientEnterCS(c) ==
    /\ pc[c] = "criticalSection"
    /\ GrantMsgValue \in BagToSet(network[c])
    /\ pc' = [pc EXCEPT ![c] = "unlock"]
    /\ hasLock' = [hasLock EXCEPT ![c] = TRUE]
    /\ network' = [network EXCEPT ![c] = RemoveFromBag(GrantMsgValue, network[c])]
    /\ UNCHANGED <<q>>

ClientUnlock(c) ==
    /\ pc[c] = "unlock"
    /\ pc' = [pc EXCEPT ![c] = "Done"]
    /\ hasLock' = [hasLock EXCEPT ![c] = FALSE]
    /\ LET msg == [type |-> "Unlock", from |-> c] IN
       network' = [network EXCEPT ![Server] = network[Server] \cup Bag({msg})]
    /\ UNCHANGED <<q>>

ServerProcessMsg(srv) ==
    /\ pc[srv] = "serverLoop"
    /\ \E msg \in BagToSet(network[srv]):
        /\ LET network_after_recv == [network EXCEPT ![srv] = RemoveFromBag(msg, network[srv])] IN
           IF msg.type = "Lock" THEN
               /\ q' = Append(q, msg.from)
               /\ IF q = <<>> THEN
                   /\ network' = [network_after_recv EXCEPT ![msg.from] = network_after_recv[msg.from] \cup Bag({GrantMsgValue})]
               ELSE
                   /\ network' = network_after_recv
               /\ UNCHANGED <<pc, hasLock>>
           ELSE /\ msg.type = "Unlock"
               /\ q' = Tail(q)
               /\ IF Tail(q) /= <<>> THEN
                   /\ LET next_client == Head(Tail(q)) IN
                   /\ network' = [network_after_recv EXCEPT ![next_client] = network_after_recv[next_client] \cup Bag({GrantMsgValue})]
               ELSE
                   /\ network' = network_after_recv
               /\ UNCHANGED <<pc, hasLock>>

Next ==
    \/ (\E c \in Client :
            \/ ClientAcquireLock(c)
            \/ ClientEnterCS(c)
            \/ ClientUnlock(c))
    \/ ServerProcessMsg(Server)

Fairness ==
    /\ WF_vars(ServerProcessMsg(Server))
    /\ \A c \in Client :
        /\ WF_vars(ClientAcquireLock(c))
        /\ WF_vars(ClientEnterCS(c))
        /\ WF_vars(ClientUnlock(c))

Spec == Init /\ [][Next]_vars /\ Fairness

====