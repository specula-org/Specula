---- MODULE locksvc ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANT NumClients
ASSUME NumClients \in Nat \ {0}

ServerID == 0
ServerSet == {ServerID}
ClientSet == 1..NumClients
NodeSet == ServerSet \cup ClientSet

LockMsg == 1
UnlockMsg == 2
GrantMsg == 3

RequestMsg == [type: {LockMsg, UnlockMsg}, from: ClientSet]
Message == RequestMsg \cup {GrantMsg}

VARIABLES pc, network, q, msg, hasLock

vars == <<pc, network, q, msg, hasLock>>

TypeOK ==
    /\ pc \in [NodeSet -> {"serverLoop", "serverReceive", "serverRespond", "acquireLock", "criticalSection", "unlock", "Done"}]
    /\ network \in [NodeSet -> Bag(Message)]
    /\ q \in Seq(ClientSet)
    /\ msg \in Message \cup {[type |-> 0, from |-> 0]}
    /\ hasLock \in [ClientSet -> BOOLEAN]

Init ==
    /\ pc = [n \in NodeSet |-> IF n = ServerID THEN "serverLoop" ELSE "acquireLock"]
    /\ network = [n \in NodeSet |-> EmptyBag]
    /\ q = <<>>
    /\ msg = [type |-> 0, from |-> 0]
    /\ hasLock = [c \in ClientSet |-> FALSE]

\* Server Actions

ServerLoop(s) ==
    /\ s = ServerID
    /\ pc[s] = "serverLoop"
    /\ pc' = [pc EXCEPT ![s] = "serverReceive"]
    /\ UNCHANGED <<network, q, msg, hasLock>>

ServerReceive(s) ==
    /\ s = ServerID
    /\ pc[s] = "serverReceive"
    /\ \E m \in network[s]:
        /\ msg' = m
        /\ network' = [network EXCEPT ![s] = network[s] \ {m}]
        /\ pc' = [pc EXCEPT ![s] = "serverRespond"]
    /\ UNCHANGED <<q, hasLock>>

ServerRespondLock(s) ==
    /\ s = ServerID
    /\ pc[s] = "serverRespond"
    /\ msg.type = LockMsg
    /\ q' = Append(q, msg.from)
    /\ network' = IF Len(q) = 0
                  THEN [network EXCEPT ![msg.from] = network[msg.from] \cup {GrantMsg}]
                  ELSE network
    /\ pc' = [pc EXCEPT ![s] = "serverLoop"]
    /\ UNCHANGED <<msg, hasLock>>

ServerRespondUnlock(s) ==
    /\ s = ServerID
    /\ pc[s] = "serverRespond"
    /\ msg.type = UnlockMsg
    /\ Len(q) > 0
    /\ LET new_q == Tail(q) IN
       /\ q' = new_q
       /\ network' = IF Len(new_q) > 0
                     THEN [network EXCEPT ![Head(new_q)] = network[Head(new_q)] \cup {GrantMsg}]
                     ELSE network
    /\ pc' = [pc EXCEPT ![s] = "serverLoop"]
    /\ UNCHANGED <<msg, hasLock>>

ServerRespondOther(s) ==
    /\ s = ServerID
    /\ pc[s] = "serverRespond"
    /\ msg.type \notin {LockMsg, UnlockMsg}
    /\ pc' = [pc EXCEPT ![s] = "serverLoop"]
    /\ UNCHANGED <<network, q, msg, hasLock>>

\* Client Actions

ClientAcquireLock(c) ==
    /\ c \in ClientSet
    /\ pc[c] = "acquireLock"
    /\ LET req == [type |-> LockMsg, from |-> c] IN
       network' = [network EXCEPT ![ServerID] = network[ServerID] \cup {req}]
    /\ pc' = [pc EXCEPT ![c] = "criticalSection"]
    /\ UNCHANGED <<q, msg, hasLock>>

ClientEnterCS(c) ==
    /\ c \in ClientSet
    /\ pc[c] = "criticalSection"
    /\ GrantMsg \in network[c]
    /\ network' = [network EXCEPT ![c] = network[c] \ {GrantMsg}]
    /\ hasLock' = [hasLock EXCEPT ![c] = TRUE]
    /\ pc' = [pc EXCEPT ![c] = "unlock"]
    /\ UNCHANGED <<q, msg>>

ClientUnlock(c) ==
    /\ c \in ClientSet
    /\ pc[c] = "unlock"
    /\ hasLock' = [hasLock EXCEPT ![c] = FALSE]
    /\ LET req == [type |-> UnlockMsg, from |-> c] IN
       network' = [network EXCEPT ![ServerID] = network[ServerID] \cup {req}]
    /\ pc' = [pc EXCEPT ![c] = "Done"]
    /\ UNCHANGED <<q, msg>>

Server(s) ==
    \/ ServerLoop(s)
    \/ ServerReceive(s)
    \/ ServerRespondLock(s)
    \/ ServerRespondUnlock(s)
    \/ ServerRespondOther(s)

Client(c) ==
    \/ ClientAcquireLock(c)
    \/ ClientEnterCS(c)
    \/ ClientUnlock(c)

Next ==
    \/ Server(ServerID)
    \/ \E c \in ClientSet : Client(c)

Fairness ==
    /\ WF_vars(Server(ServerID))
    /\ \A c \in ClientSet : WF_vars(Client(c))

Spec == Init /\ [][Next]_vars /\ Fairness

====