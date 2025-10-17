---- MODULE locksvc ----
EXTENDS Sequences, Naturals, FiniteSets, Temporal
CONSTANTS NumClients
LockMsgType == 1
UnlockMsgType == 2
GrantMsgType == 3
MsgType == {LockMsgType, UnlockMsgType, GrantMsgType}
Server == {0}
Clients == 1..NumClients
Nodes == Server \union Clients
Message == [type : MsgType, from : Nodes]
VARIABLES queue, hasLock, network, clientState
vars == <<queue, hasLock, network, clientState>>
Init == 
  /\ queue = <<>>
  /\ hasLock = [c \in Clients |-> FALSE]
  /\ network = [n \in Nodes |-> {}]
  /\ clientState = [c \in Clients |-> "acquireLock"]
TypeOK == 
  /\ queue \in Seq(Clients)
  /\ hasLock \in [Clients -> BOOLEAN]
  /\ network \in [Nodes -> SUBSET Message]
  /\ clientState \in [Clients -> {"acquireLock", "waiting", "criticalSection", "unlock", "Done"}]
ClientSendLock(c) == 
  /\ clientState[c] = "acquireLock"
  /\ network' = [network EXCEPT ![0] = @ \cup {[type |-> LockMsgType, from |-> c]}]
  /\ clientState' = [clientState EXCEPT ![c] = "waiting"]
  /\ UNCHANGED <<queue, hasLock>>
ClientReceiveGrant(c) == 
  /\ clientState[c] = "waiting"
  /\ \E m \in network[c] : m.type = GrantMsgType /\ m.from \in Server
  /\ LET m == CHOOSE m \in network[c] : m.type = GrantMsgType /\ m.from \in Server IN
     network' = [network EXCEPT ![c] = @ \ {m}]
  /\ hasLock' = [hasLock EXCEPT ![c] = TRUE]
  /\ clientState' = [clientState EXCEPT ![c] = "criticalSection"]
  /\ UNCHANGED queue
ClientSendUnlock(c) == 
  /\ clientState[c] = "criticalSection"
  /\ hasLock' = [hasLock EXCEPT ![c] = FALSE]
  /\ network' = [network EXCEPT ![0] = @ \cup {[type |-> UnlockMsgType, from |-> c]}]
  /\ clientState' = [clientState EXCEPT ![c] = "Done"]
  /\ UNCHANGED queue
ServerReceiveLock == 
  \E m \in network[0] : 
    /\ m.type = LockMsgType
    /\ LET fromClient == m.from IN
       /\ IF queue = <<>> THEN
             /\ network' = [network EXCEPT ![0] = @ \ {m}, ![fromClient] = @ \cup {[type |-> GrantMsgType, from |-> 0]}]
             /\ queue' = queue
          ELSE
             /\ network' = [network EXCEPT ![0] = @ \ {m}]
             /\ queue' = Append(queue, fromClient)
       /\ UNCHANGED <<hasLock, clientState>>
ServerReceiveUnlock == 
  \E m \in network[0] : 
    /\ m.type = UnlockMsgType
    /\ LET tempNetwork == [network EXCEPT ![0] = @ \ {m}] IN
       IF queue /= <<>> THEN
             /\ network' = [tempNetwork EXCEPT ![Head(queue)] = @ \cup {[type |-> GrantMsgType, from |-> 0]}]
             /\ queue' = Tail(queue)
          ELSE
             /\ network' = tempNetwork
             /\ queue' = queue
    /\ UNCHANGED <<hasLock, clientState>>
Next == 
  \/ \E c \in Clients : ClientSendLock(c)
  \/ \E c \in Clients : ClientReceiveGrant(c)
  \/ \E c \in Clients : ClientSendUnlock(c)
  \/ ServerReceiveLock
  \/ ServerReceiveUnlock
Spec == 
  Init 
  /\ [][Next]_vars 
  /\ WF_vars(Next)
====