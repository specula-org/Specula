---- MODULE locksvc ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANT NumClients
CONSTANT ServerId

VARIABLES serverQueue, mailboxes, pc, hasLock

ClientSet == 1..NumClients
NodeSet == {ServerId} \union ClientSet
LockMsg == 1
UnlockMsg == 2
GrantMsg == 3

TypeOK == 
    /\ serverQueue \in Seq(ClientSet)
    /\ mailboxes \in [NodeSet -> Seq([type: {LockMsg, UnlockMsg, GrantMsg}, from: NodeSet])]
    /\ pc \in [ClientSet -> {"acquireLock", "waitingGrant", "unlock", "Done"}]
    /\ hasLock \in [ClientSet -> BOOLEAN]

Init == 
    /\ serverQueue = <<>>
    /\ mailboxes = [n \in NodeSet |-> <<>>]
    /\ pc = [c \in ClientSet |-> "acquireLock"]
    /\ hasLock = [c \in ClientSet |-> FALSE]

ClientSendLock(c) ==
    /\ pc[c] = "acquireLock"
    /\ mailboxes' = [mailboxes EXCEPT ![ServerId] = Append(@, [type |-> LockMsg, from |-> c])]
    /\ pc' = [pc EXCEPT ![c] = "waitingGrant"]
    /\ UNCHANGED <<serverQueue, hasLock>>

ClientRecvGrant(c) ==
    /\ pc[c] = "waitingGrant"
    /\ mailboxes[c] /= <<>>
    /\ Head(mailboxes[c]).type = GrantMsg
    /\ mailboxes' = [mailboxes EXCEPT ![c] = Tail(@)]
    /\ hasLock' = [hasLock EXCEPT ![c] = TRUE]
    /\ pc' = [pc EXCEPT ![c] = "unlock"]
    /\ UNCHANGED serverQueue

ClientSendUnlock(c) ==
    /\ pc[c] = "unlock"
    /\ mailboxes' = [mailboxes EXCEPT ![ServerId] = Append(@, [type |-> UnlockMsg, from |-> c])]
    /\ hasLock' = [hasLock EXCEPT ![c] = FALSE]
    /\ pc' = [pc EXCEPT ![c] = "Done"]
    /\ UNCHANGED serverQueue

ServerStep ==
    /\ mailboxes[ServerId] /= <<>>
    /\ LET msg == Head(mailboxes[ServerId]) IN
        LET newMailboxes == [mailboxes EXCEPT ![ServerId] = Tail(@)] IN
        \/ /\ msg.type = LockMsg
           /\ \/ /\ serverQueue = <<>>
                 /\ newMailboxes2 == [newMailboxes EXCEPT ![msg.from] = Append(@, [type |-> GrantMsg, from |-> ServerId])]
              \/ /\ serverQueue /= <<>>
                 /\ newMailboxes2 == newMailboxes
           /\ serverQueue' = Append(serverQueue, msg.from)
        \/ /\ msg.type = UnlockMsg
           /\ serverQueue' = Tail(serverQueue)
           /\ \/ /\ serverQueue' /= <<>>
                 /\ newMailboxes2 == [newMailboxes EXCEPT ![Head(serverQueue')] = Append(@, [type |-> GrantMsg, from |-> ServerId])]
              \/ /\ serverQueue' = <<>>
                 /\ newMailboxes2 == newMailboxes
    /\ mailboxes' = newMailboxes2
    /\ UNCHANGED <<pc, hasLock>>

Next == 
    \/ \E c \in ClientSet: ClientSendLock(c)
    \/ \E c \in ClientSet: ClientRecvGrant(c)
    \/ \E c \in ClientSet: ClientSendUnlock(c)
    \/ ServerStep

Spec == 
    Init 
    /\ [][Next]_<<serverQueue, mailboxes, pc, hasLock>>
    /\ WF_<<serverQueue, mailboxes, pc, hasLock>>(ServerStep)
    /\ \A c \in ClientSet: 
            WF_<<serverQueue, mailboxes, pc, hasLock>>(ClientSendLock(c))
            /\ WF_<<serverQueue, mailboxes, pc, hasLock>>(ClientRecvGrant(c))
            /\ WF_<<serverQueue, mailboxes, pc, hasLock>>(ClientSendUnlock(c))

====