---- MODULE locksvc ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS NumClients, Server

ASSUME NumClients \in Nat \ {0}
ASSUME Server = 0

Client == 1..NumClients
Node == {Server} \cup Client

LockMsgType == 1
UnlockMsgType == 2
GrantMsgType == 3

RequestMsg == [from: Client, type: {LockMsgType, UnlockMsgType}]
Message == RequestMsg \cup {GrantMsgType}

VARIABLES pc, network, q, hasLock

vars == <<pc, network, q, hasLock>>

ClientStates == {"acquireLock", "criticalSection", "unlock", "Done"}
ServerStates == {"serverLoop"}

TypeOK ==
    /\ pc \in [Node -> IF self \in {Server} THEN ServerStates ELSE ClientStates]
    /\ network \in [Node -> Bag(Message)]
    /\ q \in Seq(Client)
    /\ hasLock \in [Client -> BOOLEAN]

Init ==
    /\ pc = [n \in Node |-> IF n = Server THEN "serverLoop" ELSE "acquireLock"]
    /\ network = [n \in Node |-> EmptyBag]
    /\ q = <<>>
    /\ hasLock = [c \in Client |-> FALSE]

ServerProcessMsg(self) ==
    /\ self = Server
    /\ pc[self] = "serverLoop"
    /\ \E msg \in network[self]:
        /\ LET network_ == [network EXCEPT ![self] = network[self] \ {msg}] IN
            /\ IF msg \in RequestMsg THEN
                /\ IF msg.type = LockMsgType THEN
                    /\ LET q_ == Append(q, msg.from) IN
                    /\ q' = q_
                    /\ IF q = <<>> THEN
                        /\ network' = [network_ EXCEPT ![msg.from] = network_[msg.from] \cup {GrantMsgType}]
                    ELSE
                        /\ network' = network_
                ELSE
                    /\ LET q_ == Tail(q) IN
                    /\ q' = q_
                    /\ IF q_ /= <<>> THEN
                        /\ network' = [network_ EXCEPT ![Head(q_)] = network_[Head(q_)] \cup {GrantMsgType}]
                    ELSE
                        /\ network' = network_
            ELSE
                /\ network' = network_
                /\ UNCHANGED <<q>>
    /\ UNCHANGED <<pc, hasLock>>

ClientAcquire(self) ==
    /\ self \in Client
    /\ pc[self] = "acquireLock"
    /\ LET msg == [from |-> self, type |-> LockMsgType] IN
       network' = [network EXCEPT ![Server] = network[Server] \cup {msg}]
    /\ pc' = [pc EXCEPT ![self] = "criticalSection"]
    /\ UNCHANGED <<q, hasLock>>

ClientEnterCS(self) ==
    /\ self \in Client
    /\ pc[self] = "criticalSection"
    /\ GrantMsgType \in network[self]
    /\ network' = [network EXCEPT ![self] = network[self] \ {GrantMsgType}]
    /\ hasLock' = [hasLock EXCEPT ![self] = TRUE]
    /\ pc' = [pc EXCEPT ![self] = "unlock"]
    /\ UNCHANGED <<q>>

ClientUnlock(self) ==
    /\ self \in Client
    /\ pc[self] = "unlock"
    /\ hasLock' = [hasLock EXCEPT ![self] = FALSE]
    /\ LET msg == [from |-> self, type |-> UnlockMsgType] IN
       network' = [network EXCEPT ![Server] = network[Server] \cup {msg}]
    /\ pc' = [pc EXCEPT ![self] = "Done"]
    /\ UNCHANGED <<q>>

Next ==
    \/ ServerProcessMsg(Server)
    \/ \E c \in Client :
        \/ ClientAcquire(c)
        \/ ClientEnterCS(c)
        \/ ClientUnlock(c)

Fairness ==
    /\ WF_vars(ServerProcessMsg(Server))
    /\ \A c \in Client : WF_vars(ClientEnterCS(c))
    /\ \A c \in Client : WF_vars(ClientUnlock(c))

Spec == Init /\ [][Next]_vars /\ Fairness

====