---- MODULE locksvc ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANT NumClients

ServerID == 0
ServerSet == {ServerID}
ClientSet == 1..NumClients
NodeSet == ServerSet \cup ClientSet

LockMsg == 1
UnlockMsg == 2
GrantMsg == 3

Msg(c, t) == [type |-> t, from |-> c]

AllMsg ==
  {GrantMsg}
  \cup { Msg(c, LockMsg) : c \in ClientSet }
  \cup { Msg(c, UnlockMsg) : c \in ClientSet }

EmptyBag == [m \in AllMsg |-> 0]
Add(b, m) == [b EXCEPT ![m] = b[m] + 1]
Remove(b, m) == [b EXCEPT ![m] = b[m] - 1]
Support(b) == {m \in AllMsg : b[m] > 0}

StageStates == {"Init", "Waiting", "CS", "Done"}

VARIABLES q, hasLock, inbox, stage

Vars == << q, hasLock, inbox, stage >>

TypeOK ==
  /\ q \in Seq(ClientSet)
  /\ hasLock \in [ClientSet -> BOOLEAN]
  /\ inbox \in [NodeSet -> [AllMsg -> Nat]]
  /\ stage \in [ClientSet -> StageStates]

Init ==
  /\ q = << >>
  /\ hasLock = [c \in ClientSet |-> FALSE]
  /\ inbox = [n \in NodeSet |-> EmptyBag]
  /\ stage = [c \in ClientSet |-> "Init"]

ClientSendLock(c) ==
  /\ c \in ClientSet
  /\ stage[c] = "Init"
  /\ inbox' = [inbox EXCEPT ![ServerID] = Add(@, Msg(c, LockMsg))]
  /\ stage' = [stage EXCEPT ![c] = "Waiting"]
  /\ UNCHANGED << q, hasLock >>

ClientReceiveGrant(c) ==
  /\ c \in ClientSet
  /\ stage[c] = "Waiting"
  /\ inbox[c][GrantMsg] > 0
  /\ inbox' = [inbox EXCEPT ![c] = Remove(@, GrantMsg)]
  /\ stage' = [stage EXCEPT ![c] = "CS"]
  /\ hasLock' = [hasLock EXCEPT ![c] = TRUE]
  /\ UNCHANGED q

ClientUnlock(c) ==
  /\ c \in ClientSet
  /\ stage[c] = "CS"
  /\ inbox' = [inbox EXCEPT ![ServerID] = Add(@, Msg(c, UnlockMsg))]
  /\ stage' = [stage EXCEPT ![c] = "Done"]
  /\ hasLock' = [hasLock EXCEPT ![c] = FALSE]
  /\ UNCHANGED q

ServerReceiveLock ==
  \E c \in ClientSet:
    /\ inbox[ServerID][Msg(c, LockMsg)] > 0
    /\ q' = Append(q, c)
    /\ inbox' =
         [inbox EXCEPT
            ![ServerID] = Remove(@, Msg(c, LockMsg)),
            ![c] = IF Len(q) = 0 THEN Add(@, GrantMsg) ELSE @]
    /\ UNCHANGED << hasLock, stage >>

ServerReceiveUnlock ==
  \E c \in ClientSet:
    /\ inbox[ServerID][Msg(c, UnlockMsg)] > 0
    /\ Len(q) > 0
    /\ LET newq == Tail(q) IN
         /\ q' = newq
         /\ inbox' =
              IF Len(newq) > 0 THEN
                [inbox EXCEPT
                   ![ServerID] = Remove(@, Msg(c, UnlockMsg)),
                   ![Head(newq)] = Add(@, GrantMsg)]
              ELSE
                [inbox EXCEPT
                   ![ServerID] = Remove(@, Msg(c, UnlockMsg))]
    /\ UNCHANGED << hasLock, stage >>

Next ==
  \/ \E c \in ClientSet: ClientSendLock(c)
  \/ \E c \in ClientSet: ClientReceiveGrant(c)
  \/ \E c \in ClientSet: ClientUnlock(c)
  \/ ServerReceiveLock
  \/ ServerReceiveUnlock

Spec ==
  /\ Init
  /\ [][Next]_Vars
  /\ \A c \in ClientSet: WF_Vars(ClientSendLock(c))
  /\ \A c \in ClientSet: WF_Vars(ClientReceiveGrant(c))
  /\ \A c \in ClientSet: WF_Vars(ClientUnlock(c))
  /\ WF_Vars(ServerReceiveLock)
  /\ WF_Vars(ServerReceiveUnlock)
====