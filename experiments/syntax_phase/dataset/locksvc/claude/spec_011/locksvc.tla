---- MODULE locksvc ----

EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS NumClients

VARIABLES 
    network,
    serverQueue,
    hasLock,
    clientState

Vars == <<network, serverQueue, hasLock, clientState>>

ServerID == 0
ClientSet == 1..NumClients
NodeSet == {ServerID} \cup ClientSet

LockMsg == 1
UnlockMsg == 2
GrantMsg == 3

TypeOK ==
    /\ network \in [NodeSet -> Seq(Nat \cup [from: NodeSet, type: {LockMsg, UnlockMsg}])]
    /\ serverQueue \in Seq(ClientSet)
    /\ hasLock \in [ClientSet -> BOOLEAN]
    /\ clientState \in [ClientSet -> {"acquiring", "critical", "unlocking", "done"}]

Init ==
    /\ network = [n \in NodeSet |-> <<>>]
    /\ serverQueue = <<>>
    /\ hasLock = [c \in ClientSet |-> FALSE]
    /\ clientState = [c \in ClientSet |-> "acquiring"]

SendMessage(from, to, msg) ==
    network' = [network EXCEPT ![to] = Append(@, msg)]

ReceiveMessage(node) ==
    /\ Len(network[node]) > 0
    /\ network' = [network EXCEPT ![node] = Tail(@)]
    /\ Head(network[node])

ClientAcquireLock(c) ==
    /\ clientState[c] = "acquiring"
    /\ SendMessage(c, ServerID, [from |-> c, type |-> LockMsg])
    /\ clientState' = [clientState EXCEPT ![c] = "critical"]
    /\ UNCHANGED <<serverQueue, hasLock>>

ClientCriticalSection(c) ==
    /\ clientState[c] = "critical"
    /\ Len(network[c]) > 0
    /\ LET msg == Head(network[c]) IN
        /\ msg = GrantMsg
        /\ network' = [network EXCEPT ![c] = Tail(@)]
        /\ hasLock' = [hasLock EXCEPT ![c] = TRUE]
        /\ clientState' = [clientState EXCEPT ![c] = "unlocking"]
        /\ UNCHANGED serverQueue

ClientUnlock(c) ==
    /\ clientState[c] = "unlocking"
    /\ hasLock[c] = TRUE
    /\ hasLock' = [hasLock EXCEPT ![c] = FALSE]
    /\ SendMessage(c, ServerID, [from |-> c, type |-> UnlockMsg])
    /\ clientState' = [clientState EXCEPT ![c] = "done"]
    /\ UNCHANGED serverQueue

ServerReceiveLock ==
    /\ Len(network[ServerID]) > 0
    /\ LET msg == Head(network[ServerID]) IN
        /\ msg.type = LockMsg
        /\ network' = [network EXCEPT ![ServerID] = Tail(@)]
        /\ IF serverQueue = <<>>
           THEN /\ network' = [network' EXCEPT ![msg.from] = Append(@, GrantMsg)]
                /\ serverQueue' = Append(serverQueue, msg.from)
           ELSE /\ serverQueue' = Append(serverQueue, msg.from)
                /\ UNCHANGED network'
        /\ UNCHANGED <<hasLock, clientState>>

ServerReceiveUnlock ==
    /\ Len(network[ServerID]) > 0
    /\ LET msg == Head(network[ServerID]) IN
        /\ msg.type = UnlockMsg
        /\ network' = [network EXCEPT ![ServerID] = Tail(@)]
        /\ serverQueue' = Tail(serverQueue)
        /\ IF Len(serverQueue') > 0
           THEN network' = [network' EXCEPT ![Head(serverQueue')] = Append(@, GrantMsg)]
           ELSE UNCHANGED network'
        /\ UNCHANGED <<hasLock, clientState>>

Next ==
    \/ \E c \in ClientSet : ClientAcquireLock(c)
    \/ \E c \in ClientSet : ClientCriticalSection(c)
    \/ \E c \in ClientSet : ClientUnlock(c)
    \/ ServerReceiveLock
    \/ ServerReceiveUnlock

Spec == Init /\ [][Next]_Vars /\ WF_Vars(ServerReceiveLock) /\ WF_Vars(ServerReceiveUnlock) /\ \A c \in ClientSet : WF_Vars(ClientUnlock(c))

====