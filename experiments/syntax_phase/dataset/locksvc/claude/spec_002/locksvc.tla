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
    /\ network \in [Nodes -> Bag([type: {LockMsg, UnlockMsg, GrantMsg}, from: Nodes])]
    /\ pc \in [Nodes -> STRING]

Init ==
    /\ hasLock = [c \in Clients |-> FALSE]
    /\ queue = <<>>
    /\ network = [n \in Nodes |-> EmptyBag]
    /\ pc = [n \in Nodes |-> IF n = ServerID THEN "serverLoop" ELSE "acquireLock"]

RequestLock(c) ==
    /\ c \in Clients
    /\ pc[c] = "acquireLock"
    /\ network' = [network EXCEPT ![ServerID] = @ (+) SetToBag({[type |-> LockMsg, from |-> c]})]
    /\ pc' = [pc EXCEPT ![c] = "criticalSection"]
    /\ UNCHANGED <<hasLock, queue>>

ProcessLockMsg ==
    /\ pc[ServerID] = "serverLoop"
    /\ \E msg \in BagToSet(network[ServerID]):
        /\ msg.type = LockMsg
        /\ network' = [network EXCEPT ![ServerID] = @ (-) SetToBag({msg})]
        /\ IF queue = <<>>
           THEN /\ network' = [network' EXCEPT ![msg.from] = @ (+) SetToBag({[type |-> GrantMsg, from |-> ServerID]})]
                /\ queue' = Append(queue, msg.from)
           ELSE /\ queue' = Append(queue, msg.from)
                /\ UNCHANGED network
    /\ UNCHANGED <<hasLock, pc>>

ProcessUnlockMsg ==
    /\ pc[ServerID] = "serverLoop"
    /\ \E msg \in BagToSet(network[ServerID]):
        /\ msg.type = UnlockMsg
        /\ network' = [network EXCEPT ![ServerID] = @ (-) SetToBag({msg})]
        /\ queue' = Tail(queue)
        /\ IF queue' # <<>>
           THEN network' = [network' EXCEPT ![Head(queue')] = @ (+) SetToBag({[type |-> GrantMsg, from |-> ServerID]})]
           ELSE UNCHANGED network
    /\ UNCHANGED <<hasLock, pc>>

ReceiveGrant(c) ==
    /\ c \in Clients
    /\ pc[c] = "criticalSection"
    /\ \E msg \in BagToSet(network[c]):
        /\ msg.type = GrantMsg
        /\ network' = [network EXCEPT ![c] = @ (-) SetToBag({msg})]
        /\ hasLock' = [hasLock EXCEPT ![c] = TRUE]
        /\ pc' = [pc EXCEPT ![c] = "unlock"]
    /\ UNCHANGED queue

ReleaseLock(c) ==
    /\ c \in Clients
    /\ pc[c] = "unlock"
    /\ hasLock[c] = TRUE
    /\ hasLock' = [hasLock EXCEPT ![c] = FALSE]
    /\ network' = [network EXCEPT ![ServerID] = @ (+) SetToBag({[type |-> UnlockMsg, from |-> c]})]
    /\ pc' = [pc EXCEPT ![c] = "Done"]
    /\ UNCHANGED queue

Next ==
    \/ \E c \in Clients: RequestLock(c)
    \/ ProcessLockMsg
    \/ ProcessUnlockMsg
    \/ \E c \in Clients: ReceiveGrant(c)
    \/ \E c \in Clients: ReleaseLock(c)

Spec == Init /\ [][Next]_vars /\ WF_vars(\E c \in Clients: ReleaseLock(c))

====