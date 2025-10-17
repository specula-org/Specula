---- MODULE locksvc ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANT NumClients
ASSUME NumClients \in Nat \ {{0}}

ServerID == 0
ServerSet == {{ServerID}}
ClientSet == 1..NumClients
NodeSet == ServerSet \cup ClientSet

LockMsg == 1
UnlockMsg == 2
GrantMsg == 3

RequestMsgBody == [from: ClientSet, type: {{LockMsg, UnlockMsg}}]
Message == {{GrantMsg}} \cup RequestMsgBody

VARIABLES pc, network, q, msg, hasLock

vars == <<pc, network, q, msg, hasLock>>

ClientPC == {{"acquireLock", "criticalSection", "unlock", "Done"}}
ServerPC == {{"serverLoop", "serverReceive", "serverRespond"}}

TypeOK ==
    /\ \A n \in NodeSet : pc[n] \in (IF n \in ServerSet THEN ServerPC ELSE ClientPC)
    /\ network \in [NodeSet -> Bags(Message)]
    /\ q \in Seq(ClientSet)
    /\ msg \in Message \cup {{[from |-> 0, type |-> 0]}}
    /\ hasLock \in [ClientSet -> BOOLEAN]

Init ==
    /\ pc = [n \in NodeSet |-> IF n \in ServerSet THEN "serverLoop" ELSE "acquireLock"]
    /\ network = [n \in NodeSet |-> EmptyBag]
    /\ q = <<>>
    /\ msg = [from |-> 0, type |-> 0]
    /\ hasLock = [c \in ClientSet |-> FALSE]

ServerLoop(self) ==
    /\ self = ServerID
    /\ pc[self] = "serverLoop"
    /\ pc' = [pc EXCEPT ![self] = "serverReceive"]
    /\ UNCHANGED <<network, q, msg, hasLock>>

ServerReceive(self) ==
    /\ self = ServerID
    /\ pc[self] = "serverReceive"
    /\ \E m \in BagToSet(network[self]):
        /\ network' = [network EXCEPT ![self] = @ (-) SetToBag({m})]
        /\ msg' = m
        /\ pc' = [pc EXCEPT ![self] = "serverRespond"]
        /\ UNCHANGED <<q, hasLock>>

ServerRespondLock(self) ==
    /\ self = ServerID
    /\ pc[self] = "serverRespond"
    /\ msg.type = LockMsg
    /\ LET new_q == Append(q, msg.from)
       IN /\ q' = new_q
          /\ network' = IF q = <<>>
                        THEN [network EXCEPT ![msg.from] = @ \u SetToBag({GrantMsg})]
                        ELSE network
    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
    /\ UNCHANGED <<msg, hasLock>>

ServerRespondUnlock(self) ==
    /\ self = ServerID
    /\ pc[self] = "serverRespond"
    /\ msg.type = UnlockMsg
    /\ q /= <<>>
    /\ LET new_q == Tail(q)
       IN /\ q' = new_q
          /\ network' = IF new_q /= <<>>
                        THEN [network EXCEPT ![Head(new_q)] = @ \u SetToBag({GrantMsg})]
                        ELSE network
    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
    /\ UNCHANGED <<msg, hasLock>>

ServerRespondOther(self) ==
    /\ self = ServerID
    /\ pc[self] = "serverRespond"
    /\ msg.type \notin {{LockMsg, UnlockMsg}}
    /\ pc' = [pc EXCEPT ![self] = "serverLoop"]
    /\ UNCHANGED <<network, q, msg, hasLock>>

ServerRespond(self) ==
    ServerRespondLock(self) \/ ServerRespondUnlock(self) \/ ServerRespondOther(self)

Server(self) ==
    ServerLoop(self) \/ ServerReceive(self) \/ ServerRespond(self)

ClientAcquireLock(self) ==
    /\ self \in ClientSet
    /\ pc[self] = "acquireLock"
    /\ LET m == [from |-> self, type |-> LockMsg]
       IN network' = [network EXCEPT ![ServerID] = @ \u SetToBag({m})]
    /\ pc' = [pc EXCEPT ![self] = "criticalSection"]
    /\ UNCHANGED <<q, msg, hasLock>>

ClientEnterCS(self) ==
    /\ self \in ClientSet
    /\ pc[self] = "criticalSection"
    /\ GrantMsg \in BagToSet(network[self])
    /\ network' = [network EXCEPT ![self] = @ (-) SetToBag({GrantMsg})]
    /\ hasLock' = [hasLock EXCEPT ![self] = TRUE]
    /\ pc' = [pc EXCEPT ![self] = "unlock"]
    /\ UNCHANGED <<q, msg>>

ClientUnlock(self) ==
    /\ self \in ClientSet
    /\ pc[self] = "unlock"
    /\ hasLock' = [hasLock EXCEPT ![self] = FALSE]
    /\ LET m == [from |-> self, type |-> UnlockMsg]
       IN network' = [network EXCEPT ![ServerID] = @ \u SetToBag({m})]
    /\ pc' = [pc EXCEPT ![self] = "Done"]
    /\ UNCHANGED <<q, msg>>

Client(self) ==
    ClientAcquireLock(self) \/ ClientEnterCS(self) \/ ClientUnlock(self)

Next ==
    \/ Server(ServerID)
    \/ \E self \in ClientSet : Client(self)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

====