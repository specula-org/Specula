---- MODULE locksvc ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS NumClients

Clients == 1..NumClients
Server == 0
Nodes == {Server} \cup Clients

Lock(c) == [type |-> "Lock", from |-> c]
Unlock(c) == [type |-> "Unlock", from |-> c]
Grant == [type |-> "Grant"]

LockMessages == { Lock(c) : c \in Clients }
UnlockMessages == { Unlock(c) : c \in Clients }

Message ==
  LockMessages \cup UnlockMessages \cup { Grant }

\* Renamed to avoid conflict with Bags module's EmptyBag
MsgEmptyBag == [m \in Message |-> 0]
MsgAddToBag(b, m) == [x \in Message |-> IF x = m THEN b[x] + 1 ELSE b[x]]
MsgRemoveOneFromBag(b, m) == [x \in Message |-> IF x = m THEN b[x] - 1 ELSE b[x]]

VARIABLES
  q,
  hasLock,
  net,
  clientState

Vars == << q, hasLock, net, clientState >>

TypeOK ==
  /\ IsSeq(q) /\ \A i \in 1..Len(q) : q[i] \in Clients \* avoid non-enumerable Seq(Clients)
  /\ hasLock \in [Clients -> BOOLEAN]
  /\ clientState \in [Clients -> {"Idle", "Waiting", "Critical", "Releasing"}]
  /\ net \in [Nodes -> [Message -> Nat]]

Init ==
  /\ TypeOK
  /\ q = << >>
  /\ hasLock = [c \in Clients |-> FALSE]
  /\ clientState = [c \in Clients |-> "Idle"]
  /\ net = [n \in Nodes |-> MsgEmptyBag]

InQueue(c) == \E i \in 1..Len(q) : q[i] = c

ClientSendLock(c) ==
  /\ c \in Clients
  /\ hasLock[c] = FALSE
  /\ ~InQueue(c)
  /\ net' = [net EXCEPT ![Server] = MsgAddToBag(@, Lock(c))]
  /\ clientState' = [clientState EXCEPT ![c] = "Waiting"]
  /\ UNCHANGED << q, hasLock >>

ClientReceiveGrant(c) ==
  /\ c \in Clients
  /\ clientState[c] = "Waiting"
  /\ net[c][Grant] > 0
  /\ net' = [net EXCEPT ![c] = MsgRemoveOneFromBag(@, Grant)]
  /\ hasLock' = [hasLock EXCEPT ![c] = TRUE]
  /\ clientState' = [clientState EXCEPT ![c] = "Critical"]
  /\ UNCHANGED q

ClientSendUnlock(c) ==
  /\ c \in Clients
  /\ hasLock[c] = TRUE
  /\ hasLock' = [hasLock EXCEPT ![c] = FALSE]
  /\ net' = [net EXCEPT ![Server] = MsgAddToBag(@, Unlock(c))]
  /\ clientState' = [clientState EXCEPT ![c] = "Releasing"]
  /\ UNCHANGED q

ClientDoneRelease(c) ==
  /\ c \in Clients
  /\ clientState[c] = "Releasing"
  /\ ~InQueue(c)
  /\ clientState' = [clientState EXCEPT ![c] = "Idle"]
  /\ UNCHANGED << q, hasLock, net >>

ServerHandleLock ==
  \E m \in LockMessages :
    /\ net[Server][m] > 0
    /\ IF q = << >>
         THEN /\ net' = [net EXCEPT ![Server] = MsgRemoveOneFromBag(@, m),
                                     ![m.from] = MsgAddToBag(@, Grant)]
              /\ q' = Append(q, m.from)
         ELSE /\ net' = [net EXCEPT ![Server] = MsgRemoveOneFromBag(@, m)]
              /\ q' = Append(q, m.from)
    /\ UNCHANGED << hasLock, clientState >>

ServerHandleUnlock ==
  \E m \in UnlockMessages :
    /\ net[Server][m] > 0
    /\ q # << >>
    /\ Head(q) = m.from
    /\ LET q1 == Tail(q) IN
         /\ IF q1 = << >>
              THEN net' = [net EXCEPT ![Server] = MsgRemoveOneFromBag(@, m)]
              ELSE net' = [net EXCEPT ![Server] = MsgRemoveOneFromBag(@, m),
                                       ![Head(q1)] = MsgAddToBag(@, Grant)]
         /\ q' = q1
    /\ UNCHANGED << hasLock, clientState >>

Next ==
  \/ \E c \in Clients : ClientSendLock(c)
  \/ \E c \in Clients : ClientReceiveGrant(c)
  \/ \E c \in Clients : ClientSendUnlock(c)
  \/ \E c \in Clients : ClientDoneRelease(c)
  \/ ServerHandleLock
  \/ ServerHandleUnlock

Spec ==
  Init /\ [][Next]_Vars
  /\ WF_Vars(ServerHandleLock)
  /\ WF_Vars(ServerHandleUnlock)
  /\ \A c \in Clients : WF_Vars(ClientReceiveGrant(c))

====