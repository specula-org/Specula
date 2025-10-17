---- MODULE locksvc ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS NumClients

ASSUME NumClients \in Nat /\ NumClients > 0

ServerID == 0
Clients == 1..NumClients
Nodes == {ServerID} \cup Clients

LockMsg == 1
UnlockMsg == 2
GrantMsg == 3

VARIABLES
    hasLock,
    queue,
    network,
    pc

vars == <<hasLock, queue, network, pc>>

TypeOK ==
    /\ hasLock \in [Clients -> BOOLEAN]
    /\ queue \in Seq(Clients)
    /\ network \in [Nodes -> [Nodes -> Seq([type: {LockMsg, UnlockMsg, GrantMsg}, from: Nodes])]]
    /\ pc \in [Nodes -> STRING]

Init ==
    /\ hasLock = [c \in Clients |-> FALSE]
    /\ queue = <<>>
    /\ network = [n \in Nodes |-> [m \in Nodes |-> <<>>]]
    /\ pc = [n \in Nodes |-> IF n = ServerID THEN "serverLoop" ELSE "acquireLock"]

RequestLock(c) ==
    /\ c \in Clients
    /\ pc[c] = "acquireLock"
    /\ network' = [network EXCEPT ![c][ServerID] = Append(@, [type |-> LockMsg, from |-> c])]
    /\ pc' = [pc EXCEPT ![c] = "waitingForGrant"]
    /\ UNCHANGED <<hasLock, queue>>

ProcessLockMsg ==
    /\ pc[ServerID] = "serverLoop"
    /\ \E c \in Clients:
        /\ network[c][ServerID] # <<>>
        /\ LET msg == Head(network[c][ServerID]) IN
            /\ msg.type = LockMsg
            /\ network' = [network EXCEPT ![c][ServerID] = Tail(@)]
            /\ IF queue = <<>>
               THEN /\ network' = [network' EXCEPT ![ServerID][msg.from] = Append(@, [type |-> GrantMsg, from |-> ServerID])]
                    /\ queue' = Append(queue, msg.from)
               ELSE /\ queue' = Append(queue, msg.from)
                    /\ UNCHANGED network'
    /\ UNCHANGED <<hasLock, pc>>

ProcessUnlockMsg ==
    /\ pc[ServerID] = "serverLoop"
    /\ \E c \in Clients:
        /\ network[c][ServerID] # <<>>
        /\ LET msg == Head(network[c][ServerID]) IN
            /\ msg.type = UnlockMsg
            /\ network' = [network EXCEPT ![c][ServerID] = Tail(@)]
            /\ queue' = Tail(queue)
            /\ IF queue' # <<>>
               THEN network' = [network' EXCEPT ![ServerID][Head(queue')] = Append(@, [type |-> GrantMsg, from |-> ServerID])]
               ELSE UNCHANGED network'
    /\ UNCHANGED <<hasLock, pc>>

ReceiveGrant(c) ==
    /\ c \in Clients
    /\ pc[c] = "waitingForGrant"
    /\ network[ServerID][c] # <<>>
    /\ LET msg == Head(network[ServerID][c]) IN
        /\ msg.type = GrantMsg
        /\ network' = [network EXCEPT ![ServerID][c] = Tail(@)]
        /\ hasLock' = [hasLock EXCEPT ![c] = TRUE]
        /\ pc' = [pc EXCEPT ![c] = "criticalSection"]
    /\ UNCHANGED queue

ReleaseLock(c) ==
    /\ c \in Clients
    /\ pc[c] = "criticalSection"
    /\ hasLock[c] = TRUE
    /\ hasLock' = [hasLock EXCEPT ![c] = FALSE]
    /\ network' = [network EXCEPT ![c][ServerID] = Append(@, [type |-> UnlockMsg, from |-> c])]
    /\ pc' = [pc EXCEPT ![c] = "acquireLock"]
    /\ UNCHANGED queue

Next ==
    \/ \E c \in Clients: RequestLock(c)
    \/ ProcessLockMsg
    \/ ProcessUnlockMsg
    \/ \E c \in Clients: ReceiveGrant(c)
    \/ \E c \in Clients: ReleaseLock(c)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

====