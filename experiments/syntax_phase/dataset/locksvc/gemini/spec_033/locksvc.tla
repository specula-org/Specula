---- MODULE locksvc ----
EXTENDS Naturals, Sequences, FiniteSets, TLC, Bags

CONSTANTS NumClients, Server

ASSUME NumClients \in Nat \ {0}
ASSUME Server \notin (1..NumClients)

ClientSet == 1..NumClients
NodeSet == {Server} \cup ClientSet

VARIABLES pc, network, q, hasLock

vars == <<pc, network, q, hasLock>>

Init ==
    /\ pc = [n \in NodeSet |-> IF n = Server THEN "serverReceive" ELSE "acquireLock"]
    /\ network = [n \in NodeSet |-> EmptyBag]
    /\ q = <<>>
    /\ hasLock = [c \in ClientSet |-> FALSE]

ClientRequestLock(self) ==
    /\ pc[self] = "acquireLock"
    /\ pc' = [pc EXCEPT ![self] = "criticalSection"]
    /\ network' = [network EXCEPT ![Server] =
        network[Server] \o <<[type |-> "LockMsg", from |-> self]>>]
    /\ UNCHANGED <<q, hasLock>>

ClientReceiveGrant(self) ==
    /\ pc[self] = "criticalSection"
    /\ \E msg \in BagToSet(network[self]) : msg = "GrantMsg"
    /\ network' = [network EXCEPT ![self] = (network[self] (-.) <<"GrantMsg">>)]
    /\ hasLock' = [hasLock EXCEPT ![self] = TRUE]
    /\ pc' = [pc EXCEPT ![self] = "unlock"]
    /\ UNCHANGED <<q>>

ClientUnlock(self) ==
    /\ pc[self] = "unlock"
    /\ hasLock[self]
    /\ hasLock' = [hasLock EXCEPT ![self] = FALSE]
    /\ network' = [network EXCEPT ![Server] =
        network[Server] \o <<[type |-> "UnlockMsg", from |-> self]>>]
    /\ pc' = [pc EXCEPT ![self] = "Done"]
    /\ UNCHANGED <<q>>

ServerProcessLockMsg(self, msg) ==
    /\ self = Server
    /\ msg["type"] = "LockMsg"
    /\ LET sender == msg["from"]
           temp_network == [network EXCEPT ![self] = network[self] (-.) <<msg>>]
       IN /\ q' = Append(q, sender)
          /\ network' = IF Len(q) = 0
                        THEN [temp_network EXCEPT ![sender] = temp_network[sender] \o <<"GrantMsg">>]
                        ELSE temp_network
    /\ UNCHANGED <<pc, hasLock>>

ServerProcessUnlockMsg(self, msg) ==
    /\ self = Server
    /\ msg["type"] = "UnlockMsg"
    /\ IF Len(q) > 0
       THEN LET new_q == Tail(q)
                temp_network == [network EXCEPT ![self] = network[self] (-.) <<msg>>]
            IN /\ q' = new_q
               /\ network' = IF Len(new_q) > 0
                             THEN [temp_network EXCEPT ![Head(new_q)] = temp_network[Head(new_q)] \o <<"GrantMsg">>]
                             ELSE temp_network
       ELSE /\ q' = q
            /\ network' = [network EXCEPT ![self] = network[self] (-.) <<msg>>]
    /\ UNCHANGED <<pc, hasLock>>

Next ==
    \/ \E self \in ClientSet :
        \/ ClientRequestLock(self)
        \/ ClientReceiveGrant(self)
        \/ ClientUnlock(self)
    \/ \E msg \in BagToSet(network[Server]) :
        \/ ServerProcessLockMsg(Server, msg)
        \/ ServerProcessUnlockMsg(Server, msg)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

====