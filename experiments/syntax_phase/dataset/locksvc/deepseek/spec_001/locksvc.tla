---- MODULE locksvc ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS NumClients, ServerID
ASSUME ServerID = 0
VARIABLES mailboxes, queue, hasLock, clientState

Vars == <<mailboxes, queue, hasLock, clientState>>

NodeSet == {ServerID} \union (1..NumClients)
ClientSet == 1..NumClients
MessageType == {"Lock", "Unlock", "Grant"}

LockMsg(from) == [type |-> "Lock", from |-> from]
UnlockMsg(from) == [type |-> "Unlock", from |-> from]
GrantMsg == [type |-> "Grant"]

Init ==
    /\ mailboxes = [n \in NodeSet |-> EmptyBag]
    /\ queue = <<>>
    /\ hasLock = [c \in ClientSet |-> FALSE]
    /\ clientState = [c \in ClientSet |-> "idle"]

TypeOK ==
    /\ mailboxes \in [NodeSet -> BAG( [type: MessageType, from: ClientSet] \union [type: {"Grant"}] )]
    /\ queue \in Seq(ClientSet)
    /\ hasLock \in [ClientSet -> BOOLEAN]
    /\ clientState \in [ClientSet -> {"idle", "waiting", "critical"}]

ClientSendLock(c) ==
    /\ clientState[c] = "idle"
    /\ mailboxes' = [mailboxes EXCEPT ![ServerID] = @ (+) {LockMsg(c)}]
    /\ clientState' = [clientState EXCEPT ![c] = "waiting"]
    /\ UNCHANGED <<queue, hasLock>>

ServerReceiveLock ==
    LET msg == CHOOSE msg \in mailboxes[ServerID]: msg.type = "Lock"
    IN
    /\ msg.type = "Lock"
    /\ mailboxes' = [mailboxes EXCEPT ![ServerID] = @ \ {msg}]
    /\ IF queue = <<>>
        THEN 
            /\ mailboxes'' = [mailboxes' EXCEPT ![msg.from] = @ (+) {GrantMsg}]
            /\ queue' = Append(queue, msg.from)
            /\ mailboxes''' = mailboxes''
        ELSE
            /\ queue' = Append(queue, msg.from)
            /\ mailboxes''' = mailboxes'
    /\ UNCHANGED <<hasLock, clientState>>

ServerReceiveUnlock ==
    LET msg == CHOOSE msg \in mailboxes[ServerID]: msg.type = "Unlock"
    IN
    /\ msg.type = "Unlock"
    /\ queue /= <<>>
    /\ Head(queue) = msg.from
    /\ mailboxes' = [mailboxes EXCEPT ![ServerID] = @ \ {msg}]
    /\ queue' = Tail(queue)
    /\ IF queue' /= <<>>
        THEN 
            mailboxes'' = [mailboxes' EXCEPT ![Head(queue')] = @ (+) {GrantMsg}]
        ELSE 
            mailboxes'' = mailboxes'
    /\ UNCHANGED <<hasLock, clientState>>

ClientReceiveGrant(c) ==
    /\ clientState[c] = "waiting"
    /\ GrantMsg \in mailboxes[c]
    /\ mailboxes' = [mailboxes EXCEPT ![c] = @ \ {GrantMsg}]
    /\ hasLock' = [hasLock EXCEPT ![c] = TRUE]
    /\ clientState' = [clientState EXCEPT ![c] = "critical"]
    /\ UNCHANGED queue

ClientSendUnlock(c) ==
    /\ clientState[c] = "critical"
    /\ hasLock[c] = TRUE
    /\ hasLock' = [hasLock EXCEPT ![c] = FALSE]
    /\ mailboxes' = [mailboxes EXCEPT ![ServerID] = @ (+) {UnlockMsg(c)}]
    /\ clientState' = [clientState EXCEPT ![c] = "idle"]
    /\ UNCHANGED queue

Next ==
    \/ \E c \in ClientSet: ClientSendLock(c)
    \/ ServerReceiveLock
    \/ \E c \in ClientSet: ClientReceiveGrant(c)
    \/ \E c \in ClientSet: ClientSendUnlock(c)
    \/ ServerReceiveUnlock

Spec == Init /\ [][Next]_Vars
    /\ WF_Vars(ServerReceiveLock)
    /\ WF_Vars(ServerReceiveUnlock)
    /\ \A c \in ClientSet: WF_Vars(ClientSendLock(c))
    /\ \A c \in ClientSet: WF_Vars(ClientReceiveGrant(c))
    /\ \A c \in ClientSet: WF_Vars(ClientSendUnlock(c))

====