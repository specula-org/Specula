---- MODULE locksvc ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS NumClients

ASSUME NumClients \in Nat \ {0}

Server == 0
Client == 1..NumClients
Node == {Server} \cup Client

LockMsg(c) == [type |-> "Lock", from |-> c]
UnlockMsg(c) == [type |-> "Unlock", from |-> c]
GrantMsg == "Grant"

RequestMessage == { LockMsg(c) : c \in Client } \cup { UnlockMsg(c) : c \in Client }
Message == RequestMessage \cup {GrantMsg}

VARIABLES pc, network, hasLock, q, msg

vars == << pc, network, hasLock, q, msg >>

TypeOK ==
    /\ pc \in [Node -> {"serverLoop", "serverRespond", "acquireLock", "criticalSection", "unlock", "Done"}]
    /\ network \in [Node -> Bags(Message)]
    /\ hasLock \in [Client -> BOOLEAN]
    /\ q \in Seq(Client)
    /\ msg \in Message \cup {"Init"}

Init ==
    /\ pc = [n \in Node |-> IF n = Server THEN "serverLoop" ELSE "acquireLock"]
    /\ network = [n \in Node |-> EmptyBag]
    /\ hasLock = [c \in Client |-> FALSE]
    /\ q = <<>>
    /\ msg = "Init"

ClientRequestLock(c) ==
    /\ pc[c] = "acquireLock"
    /\ network' = [network EXCEPT ![Server] = @ \cup {LockMsg(c)}]
    /\ pc' = [pc EXCEPT ![c] = "criticalSection"]
    /\ UNCHANGED << hasLock, q, msg >>

ClientEnterCS(c) ==
    /\ pc[c] = "criticalSection"
    /\ GrantMsg \in network[c]
    /\ network' = [network EXCEPT ![c] = BagRemove(GrantMsg, @)]
    /\ hasLock' = [hasLock EXCEPT ![c] = TRUE]
    /\ pc' = [pc EXCEPT ![c] = "unlock"]
    /\ UNCHANGED << q, msg >>

ClientUnlock(c) ==
    /\ pc[c] = "unlock"
    /\ hasLock' = [hasLock EXCEPT ![c] = FALSE]
    /\ network' = [network EXCEPT ![Server] = @ \cup {UnlockMsg(c)}]
    /\ pc' = [pc EXCEPT ![c] = "Done"]
    /\ UNCHANGED << q, msg >>

Server_Receive ==
    /\ pc[Server] = "serverLoop"
    /\ \E m \in RequestMessage:
        /\ m \in network[Server]
        /\ network' = [network EXCEPT ![Server] = BagRemove(m, @)]
        /\ msg' = m
        /\ pc' = [pc EXCEPT ![Server] = "serverRespond"]
        /\ UNCHANGED << hasLock, q >>

Server_RespondLock ==
    /\ pc[Server] = "serverRespond"
    /\ msg.type = "Lock"
    /\ LET client == msg.from IN
       /\ q' = Append(q, client)
       /\ IF q = <<>> THEN
            /\ network' = [network EXCEPT ![client] = @ \cup {GrantMsg}]
       ELSE
            /\ UNCHANGED network
    /\ pc' = [pc EXCEPT ![Server] = "serverLoop"]
    /\ UNCHANGED << hasLock, msg >>

Server_RespondUnlock ==
    /\ pc[Server] = "serverRespond"
    /\ msg.type = "Unlock"
    /\ q /= <<>>
    /\ LET q_new == Tail(q) IN
       /\ q' = q_new
       /\ IF q_new /= <<>> THEN
            /\ LET next_client == Head(q_new) IN
               /\ network' = [network EXCEPT ![next_client] = @ \cup {GrantMsg}]
       ELSE
            /\ UNCHANGED network
    /\ pc' = [pc EXCEPT ![Server] = "serverLoop"]
    /\ UNCHANGED << hasLock, msg >>

Next ==
    \/ \E c \in Client:
        \/ ClientRequestLock(c)
        \/ ClientEnterCS(c)
        \/ ClientUnlock(c)
    \/ Server_Receive
    \/ Server_RespondLock
    \/ Server_RespondUnlock

Fairness ==
    /\ \A c \in Client: WF_vars(ClientRequestLock(c))
    /\ \A c \in Client: WF_vars(ClientEnterCS(c))
    /\ \A c \in Client: WF_vars(ClientUnlock(c))
    /\ WF_vars(Server_Receive)
    /\ WF_vars(Server_RespondLock)
    /\ WF_vars(Server_RespondUnlock)

Spec == Init /\ [][Next]_vars /\ Fairness

====