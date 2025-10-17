---- MODULE locksvc ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS NumClients, ServerID
LockMsg == 1
UnlockMsg == 2
GrantMsg == 3
ServerSet == {ServerID}
ClientSet == 1..NumClients
Nodes == ServerSet \cup ClientSet
Message == [type: {LockMsg, UnlockMsg, GrantMsg}, from: Nodes]

VARIABLES serverQueue, network, hasLock, pc, msg

TypeOK ==
    /\ serverQueue \in Seq(ClientSet)
    /\ network \in [Nodes -> BAG Message]
    /\ hasLock \in [ClientSet -> BOOLEAN]
    /\ pc \in [Nodes -> {"serverLoop", "serverReceive", "serverRespond", "Done", "acquireLock", "criticalSection", "unlock"}]
    /\ msg \in Message \cup {[type |-> 0, from |-> 0]}

Init ==
    /\ serverQueue = <<>>
    /\ network = [n \in Nodes |-> EmptyBag]
    /\ hasLock = [c \in ClientSet |-> FALSE]
    /\ pc = [n \in Nodes |-> IF n \in ServerSet THEN "serverLoop" ELSE "acquireLock"]
    /\ msg = [type |-> 0, from |-> 0]

ServerReceive(self) ==
    /\ pc[self] = "serverLoop"
    /\ \E m \in BagToSet(network[self]):
        /\ msg' = m
        /\ network' = [network EXCEPT ![self] = BagRemove(network[self], m)]
        /\ pc' = [pc EXCEPT ![self] = "serverRespond"]
    /\ UNCHANGED <<serverQueue, hasLock>>

ServerRespond(self) ==
    /\ pc[self] = "serverRespond"
    /\ IF msg.type = LockMsg
        THEN 
            /\ serverQueue' = IF serverQueue = <<>> THEN serverQueue ELSE Append(serverQueue, msg.from)
            /\ network' = IF serverQueue = <<>> 
                         THEN [network EXCEPT ![msg.from] = BagAdd(@, [type |-> GrantMsg, from |-> self])]
                         ELSE network
        ELSE IF msg.type = UnlockMsg
            THEN 
                /\ serverQueue' = Tail(serverQueue)
                /\ network' = IF Tail(serverQueue) # <<>> 
                             THEN [network EXCEPT ![Head(Tail(serverQueue))] = BagAdd(@, [type |-> GrantMsg, from |-> self])]
                             ELSE network
            ELSE TRUE
    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
    /\ msg' = [type |-> 0, from |-> 0]
    /\ UNCHANGED hasLock

ClientAcquireLock(self) ==
    /\ pc[self] = "acquireLock"
    /\ network' = [network EXCEPT ![ServerID] = BagAdd(network[ServerID], [type |-> LockMsg, from |-> self])]
    /\ pc' = [pc EXCEPT ![self] = "criticalSection"]
    /\ UNCHANGED <<serverQueue, hasLock, msg>>

ClientCriticalSection(self) ==
    /\ pc[self] = "criticalSection"
    /\ \E m \in BagToSet(network[self]):
        /\ m.type = GrantMsg
        /\ network' = [network EXCEPT ![self] = BagRemove(network[self], m)]
        /\ hasLock' = [hasLock EXCEPT ![self] = TRUE]
        /\ pc' = [pc EXCEPT ![self] = "unlock"]
    /\ UNCHANGED <<serverQueue, msg>>

ClientUnlock(self) ==
    /\ pc[self] = "unlock"
    /\ hasLock' = [hasLock EXCEPT ![self] = FALSE]
    /\ network' = [network EXCEPT ![ServerID] = BagAdd(network[ServerID], [type |-> UnlockMsg, from |-> self])]
    /\ pc' = [pc EXCEPT ![self] = "Done"]
    /\ UNCHANGED <<serverQueue, msg>>

Next ==
    \/ \E self \in ServerSet: ServerReceive(self) \/ ServerRespond(self)
    \/ \E self \in ClientSet: ClientAcquireLock(self) \/ ClientCriticalSection(self) \/ ClientUnlock(self)

vars == <<serverQueue, network, hasLock, pc, msg>>

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

====