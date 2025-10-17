---- MODULE locksvc ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANT NumClients
ASSUME NumClients \in Nat \ {0}

Server == 0
ServerSet == {Server}
ClientSet == 1..NumClients
NodeSet == ServerSet \cup ClientSet

LockMsg == 1
UnlockMsg == 2
GrantMsg == 3

RequestMsgType == {LockMsg, UnlockMsg}
RequestMsg == [from: ClientSet, type: RequestMsgType]
Message == RequestMsg \cup {GrantMsg}

VARIABLES pc, q, hasLock, network, server_msg

vars == <<pc, q, hasLock, network, server_msg>>

ClientStates == {"acquireLock", "criticalSection", "unlock", "Done"}
ServerStates == {"serverLoop", "serverRespond"}

TypeOK ==
    /\ pc \in [NodeSet -> IF self \in ClientSet THEN ClientStates ELSE ServerStates]
    /\ q \in Seq(ClientSet)
    /\ hasLock \in [ClientSet -> BOOLEAN]
    /\ network \in [NodeSet -> Bags(Message)]
    /\ server_msg \in (RequestMsg \cup {[from |-> 0, type |-> 0]})

Init ==
    /\ pc = [n \in NodeSet |-> IF n \in ClientSet THEN "acquireLock" ELSE "serverLoop"]
    /\ q = <<>>
    /\ hasLock = [c \in ClientSet |-> FALSE]
    /\ network = [n \in NodeSet |-> EmptyBag]
    /\ server_msg = [from |-> 0, type |-> 0]

Client_acquireLock(c) ==
    /\ pc[c] = "acquireLock"
    /\ LET msg == [from |-> c, type |-> LockMsg]
       IN network' = [network EXCEPT ![Server] = network[Server] (+) {[msg: 1]}]
    /\ pc' = [pc EXCEPT ![c] = "criticalSection"]
    /\ UNCHANGED <<q, hasLock, server_msg>>

Client_criticalSection(c) ==
    /\ pc[c] = "criticalSection"
    /\ GrantMsg \in BagToSet(network[c])
    /\ network' = [network EXCEPT ![c] = network[c] (-) {[GrantMsg: 1]}]
    /\ hasLock' = [hasLock EXCEPT ![c] = TRUE]
    /\ pc' = [pc EXCEPT ![c] = "unlock"]
    /\ UNCHANGED <<q, server_msg>>

Client_unlock(c) ==
    /\ pc[c] = "unlock"
    /\ hasLock' = [hasLock EXCEPT ![c] = FALSE]
    /\ LET msg == [from |-> c, type |-> UnlockMsg]
       IN network' = [network EXCEPT ![Server] = network[Server] (+) {[msg: 1]}]
    /\ pc' = [pc EXCEPT ![c] = "Done"]
    /\ UNCHANGED <<q, server_msg>>

AClient(c) ==
    \/ Client_acquireLock(c)
    \/ Client_criticalSection(c)
    \/ Client_unlock(c)

Server_receive ==
    /\ pc[Server] = "serverLoop"
    /\ network[Server] /= EmptyBag
    /\ \exists msg \in BagToSet(network[Server]):
        /\ network' = [network EXCEPT ![Server] = network[Server] (-) {[msg: 1]}]
        /\ server_msg' = msg
        /\ pc' = [pc EXCEPT ![Server] = "serverRespond"]
    /\ UNCHANGED <<q, hasLock>>

Server_respond ==
    /\ pc[Server] = "serverRespond"
    /\ IF server_msg.type = LockMsg
       THEN /\ q' = Append(q, server_msg.from)
            /\ network' = IF q = <<>>
                         THEN [network EXCEPT ![server_msg.from] = network[server_msg.from] (+) {[GrantMsg: 1]}]
                         ELSE network
       ELSE IF server_msg.type = UnlockMsg
            THEN /\ q' = Tail(q)
                 /\ network' = IF Tail(q) /= <<>>
                              THEN [network EXCEPT ![Head(Tail(q))] = network[Head(Tail(q))] (+) {[GrantMsg: 1]}]
                              ELSE network
            ELSE /\ q' = q
                 /\ network' = network
    /\ pc' = [pc EXCEPT ![Server] = "serverLoop"]
    /\ UNCHANGED <<hasLock, server_msg>>

AServer ==
    \/ Server_receive
    \/ Server_respond

Next ==
    \/ AServer
    \/ \exists c \in ClientSet: AClient(c)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

====