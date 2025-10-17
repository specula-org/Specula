---- MODULE locksvc ----
EXTENDS TLC, Sequences, Naturals, FiniteSets, Bags

CONSTANTS NumClients, Server
ASSUME NumClients \in Nat \ {0}
ASSUME Server \notin 1..NumClients

CONSTANT Client
ASSUME Client = 1..NumClients

Node == {Server} \cup Client

VARIABLES pc, network, q, hasLock

vars == <<pc, network, q, hasLock>>

TypeOK ==
    /\ pc \in [Node -> {"Idle", "Requesting", "Holding", "ServerLoop"}]
    /\ LET Msgs == {[type |-> "Lock", from |-> c] : c \in Client} \cup
                   {[type |-> "Unlock", from |-> c] : c \in Client} \cup
                   {[type |-> "Grant"]}
       IN network \in [Node -> Bags(Msgs)]
    /\ q \in Seq(Client)
    /\ hasLock \in [Client -> BOOLEAN]

LockMsg(sender) == [type |-> "Lock", from |-> sender]
UnlockMsg(sender) == [type |-> "Unlock", from |-> sender]
GrantMsg == [type |-> "Grant"]

Init ==
    /\ pc = [n \in Node |-> IF n = Server THEN "ServerLoop" ELSE "Idle"]
    /\ network = [n \in Node |-> EmptyBag]
    /\ q = <<>>
    /\ hasLock = [c \in Client |-> FALSE]

ClientRequestLock(c) ==
    /\ c \in Client
    /\ pc[c] = "Idle"
    /\ pc' = [pc EXCEPT ![c] = "Requesting"]
    /\ network' = [network EXCEPT ![Server] = network[Server] \cup SeqToBag(<<LockMsg(c)>>)]
    /\ UNCHANGED <<q, hasLock>>

ClientEnterCS(c) ==
    /\ c \in Client
    /\ pc[c] = "Requesting"
    /\ GrantMsg \in BagToSet(network[c])
    /\ pc' = [pc EXCEPT ![c] = "Holding"]
    /\ hasLock' = [hasLock EXCEPT ![c] = TRUE]
    /\ network' = [network EXCEPT ![c] = network[c] \X SeqToBag(<<GrantMsg>>)]
    /\ UNCHANGED <<q>>

ClientReleaseLock(c) ==
    /\ c \in Client
    /\ pc[c] = "Holding"
    /\ pc' = [pc EXCEPT ![c] = "Idle"]
    /\ hasLock' = [hasLock EXCEPT ![c] = FALSE]
    /\ network' = [network EXCEPT ![Server] = network[Server] \cup SeqToBag(<<UnlockMsg(c)>>)]
    /\ UNCHANGED <<q>>

ServerProcessLockRequest(sender) ==
    /\ sender \in Client
    /\ LockMsg(sender) \in BagToSet(network[Server])
    /\ LET new_network == [network EXCEPT ![Server] = network[Server] \X SeqToBag(<<LockMsg(sender)>>)]
           new_q == Append(q, sender)
       IN /\ IF q = <<>>
             THEN network' = [new_network EXCEPT ![sender] = new_network[sender] \cup SeqToBag(<<GrantMsg>>)]
             ELSE network' = new_network
          /\ q' = new_q
          /\ UNCHANGED <<pc, hasLock>>

ServerProcessUnlock(sender) ==
    /\ sender \in Client
    /\ UnlockMsg(sender) \in BagToSet(network[Server])
    /\ q /= <<>>
    /\ Head(q) = sender
    /\ LET new_network == [network EXCEPT ![Server] = network[Server] \X SeqToBag(<<UnlockMsg(sender)>>)]
           new_q == Tail(q)
       IN /\ IF new_q /= <<>>
             THEN LET next_client == Head(new_q)
                  IN network' = [new_network EXCEPT ![next_client] = new_network[next_client] \cup SeqToBag(<<GrantMsg>>)]
             ELSE network' = new_network
          /\ q' = new_q
          /\ UNCHANGED <<pc, hasLock>>

Next ==
    \/ \E c \in Client : ClientRequestLock(c)
    \/ \E c \in Client : ClientEnterCS(c)
    \/ \E c \in Client : ClientReleaseLock(c)
    \/ \E c \in Client : ServerProcessLockRequest(c)
    \/ \E c \in Client : ServerProcessUnlock(c)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

====
