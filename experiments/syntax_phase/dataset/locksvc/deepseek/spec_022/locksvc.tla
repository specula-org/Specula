---- MODULE locksvc ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANT NumClients
ASSUME NumClients \in Nat \ {0}

VARIABLES serverQueue, network, state

Nodes == 0..NumClients
Server == 0
Client == 1..NumClients
MessageType == {"LockMsg", "UnlockMsg", "GrantMsg"}

TypeOK == 
    /\ serverQueue \in Seq(Client)
    /\ network \in BAG([type: MessageType, from: Nodes, to: Nodes])
    /\ state \in [Client -> {"acquireLock", "waiting", "criticalSection", "releasing"}]

Init == 
    /\ serverQueue = <<>>
    /\ network = EmptyBag
    /\ state = [c \in Client |-> "acquireLock"]

ClientSendLock(c) ==
    /\ state[c] = "acquireLock"
    /\ network' = network (+) {[type |-> "LockMsg", from |-> c, to |-> Server]}
    /\ state' = [state EXCEPT ![c] = "waiting"]
    /\ UNCHANGED serverQueue

ServerReceiveLock(c) ==
    /\ \E msg \in network :
        /\ msg.type = "LockMsg"
        /\ msg.from = c
        /\ msg.to = Server
    /\ serverQueue' = Append(serverQueue, c)
    /\ LET newNet == network \ {msg} IN
        IF Len(serverQueue) = 0
            THEN network' = newNet (+) {[type |-> "GrantMsg", from |-> Server, to |-> c]}
            ELSE network' = newNet
    /\ UNCHANGED state

ClientReceiveGrant(c) ==
    /\ state[c] = "waiting"
    /\ \E msg \in network :
        /\ msg.type = "GrantMsg"
        /\ msg.to = c
        /\ msg.from = Server
    /\ network' = network \ {msg}
    /\ state' = [state EXCEPT ![c] = "criticalSection"]
    /\ UNCHANGED serverQueue

ClientRelease(c) ==
    /\ state[c] = "criticalSection"
    /\ network' = network (+) {[type |-> "UnlockMsg", from |-> c, to |-> Server]}
    /\ state' = [state EXCEPT ![c] = "releasing"]
    /\ UNCHANGED serverQueue

ServerReceiveUnlock(c) ==
    /\ \E msg \in network :
        /\ msg.type = "UnlockMsg"
        /\ msg.from = c
        /\ msg.to = Server
    /\ serverQueue # <<>>
    /\ c = Head(serverQueue)
    /\ serverQueue' = Tail(serverQueue)
    /\ LET newNet == network \ {msg} IN
        IF serverQueue' # <<>>
            THEN network' = newNet (+) {[type |-> "GrantMsg", from |-> Server, to |-> Head(serverQueue')]}
            ELSE network' = newNet
    /\ UNCHANGED state

ClientReacquire(c) ==
    /\ state[c] = "releasing"
    /\ state' = [state EXCEPT ![c] = "acquireLock"]
    /\ UNCHANGED <<serverQueue, network>>

Next == 
    \/ \E c \in Client: ClientSendLock(c)
    \/ \E c \in Client: ServerReceiveLock(c)
    \/ \E c \in Client: ClientReceiveGrant(c)
    \/ \E c \in Client: ClientRelease(c)
    \/ \E c \in Client: ServerReceiveUnlock(c)
    \/ \E c \in Client: ClientReacquire(c)

vars == <<serverQueue, network, state>>

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

====