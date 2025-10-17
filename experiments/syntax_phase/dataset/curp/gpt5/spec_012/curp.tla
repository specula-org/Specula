---- MODULE curp ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS
  R, \* set of replica ids
  PID, \* set of proposal ids
  KEY, \* set of keys
  CMDS, \* set of commands
  Keys, \* Keys \in [CMDS -> SUBSET KEY]
  NoLeader

ASSUME Keys \in [CMDS -> SUBSET KEY]
ASSUME NoLeader \notin R

ClientRespVals == {"None", "Fast", "Commit"}

N == Cardinality(R)
Quorum(n) == (n \div 2) + 1
RecoverQuorum(n) == (Quorum(n) \div 2) + 1
SuperQuorum(n) == (n - Quorum(n)) + RecoverQuorum(n)

QuorumN == Quorum(N)
RecoverQuorumN == RecoverQuorum(N)
SuperQuorumN == SuperQuorum(N)

VARIABLES
  leader,         \* leader id or NoLeader
  SpecPool,       \* [R -> SUBSET PID]
  UCP,            \* [R -> SUBSET PID]
  Committed,      \* subset of PID
  Acks,           \* [PID -> SUBSET R] non-leader record acks
  LeaderConflict, \* [PID -> BOOLEAN] leader conflict flag for pid
  Pending,        \* subset of PID that are outstanding
  UseFast,        \* [PID -> BOOLEAN]
  PidKeys,        \* [PID -> SUBSET KEY]
  ClientResp      \* [PID -> ClientRespVals]

vars == <<leader, SpecPool, UCP, Committed, Acks, LeaderConflict, Pending, UseFast, PidKeys, ClientResp>>

Init ==
  /\ leader = NoLeader
  /\ SpecPool \in [R -> SUBSET PID]
  /\ SpecPool = [r \in R |-> {}]
  /\ UCP \in [R -> SUBSET PID]
  /\ UCP = [r \in R |-> {}]
  /\ Committed = {}
  /\ Acks \in [PID -> SUBSET R]
  /\ Acks = [p \in PID |-> {}]
  /\ LeaderConflict \in [PID -> BOOLEAN]
  /\ LeaderConflict = [p \in PID |-> TRUE]
  /\ Pending \subseteq PID
  /\ Pending = {}
  /\ UseFast \in [PID -> BOOLEAN]
  /\ UseFast = [p \in PID |-> FALSE]
  /\ PidKeys \in [PID -> SUBSET KEY]
  /\ PidKeys = [p \in PID |-> {}]
  /\ ClientResp \in [PID -> ClientRespVals]
  /\ ClientResp = [p \in PID |-> "None"]

KeysOf(pid) == PidKeys[pid]

ConflictWith(keys, poolSet) == \E q \in poolSet: KeysOf(q) \cap keys # {}

OtherReplicas ==
  IF leader \in R THEN R \ {leader} ELSE R

Propose(pid, c, uf) ==
  /\ pid \in PID
  /\ c \in CMDS
  /\ uf \in BOOLEAN
  /\ pid \notin Pending
  /\ pid \notin Committed
  /\ \A r \in R: pid \notin SpecPool[r]
  /\ \A r \in R: pid \notin UCP[r]
  /\ ClientResp[pid] = "None"
  /\ PidKeys' = [PidKeys EXCEPT ![pid] = Keys(c)]
  /\ UseFast' = [UseFast EXCEPT ![pid] = uf]
  /\ Pending' = Pending \cup {pid}
  /\ UNCHANGED <<leader, SpecPool, UCP, Committed, Acks, LeaderConflict, ClientResp>>

ProcessProposeLeader(r, pid) ==
  /\ leader \in R
  /\ r = leader
  /\ pid \in Pending
  /\ LET k == PidKeys[pid] IN
     LET pool == SpecPool[leader] \cup UCP[leader] IN
     LET conflict == \E q \in pool: PidKeys[q] \cap k # {} IN
       /\ LeaderConflict' = [LeaderConflict EXCEPT ![pid] = conflict]
       /\ SpecPool' = IF ~conflict THEN [SpecPool EXCEPT ![leader] = @ \cup {pid}] ELSE SpecPool
       /\ UCP' = IF ~conflict THEN [UCP EXCEPT ![leader] = @ \cup {pid}] ELSE UCP
       /\ UNCHANGED <<leader, Committed, Acks, Pending, UseFast, PidKeys, ClientResp>>

ProcessProposeNonLeader(r, pid) ==
  /\ r \in OtherReplicas
  /\ pid \in Pending
  /\ LET k == PidKeys[pid] IN
     LET pool == SpecPool[r] IN
     LET conflict == \E q \in pool: PidKeys[q] \cap k # {} IN
       /\ IF ~conflict THEN
             /\ SpecPool' = [SpecPool EXCEPT ![r] = @ \cup {pid}]
             /\ Acks' = [Acks EXCEPT ![pid] = @ \cup {r}]
          ELSE
             /\ SpecPool' = SpecPool
             /\ Acks' = Acks
       /\ UNCHANGED <<leader, UCP, Committed, LeaderConflict, Pending, UseFast, PidKeys, ClientResp>>

DecideFast(pid) ==
  /\ pid \in Pending
  /\ ClientResp[pid] = "None"
  /\ UseFast[pid] = TRUE
  /\ LeaderConflict[pid] = FALSE
  /\ Cardinality(Acks[pid]) >= SuperQuorumN - 1
  /\ ClientResp' = [ClientResp EXCEPT ![pid] = "Fast"]
  /\ UNCHANGED <<leader, SpecPool, UCP, Committed, Acks, LeaderConflict, Pending, UseFast, PidKeys>>

Commit(pid) ==
  /\ leader \in R
  /\ pid \in UCP[leader]
  /\ pid \notin Committed
  /\ Committed' = Committed \cup {pid}
  /\ UNCHANGED <<leader, SpecPool, UCP, Acks, LeaderConflict, Pending, UseFast, PidKeys, ClientResp>>

ProcessCommitMsg(r, pid) ==
  /\ r \in R
  /\ pid \in Committed
  /\ SpecPool' = [SpecPool EXCEPT ![r] = @ \ {pid}]
  /\ UCP' = [UCP EXCEPT ![r] = @ \ {pid}]
  /\ ClientResp' = [ClientResp EXCEPT ![pid] = "Commit"]
  /\ UNCHANGED <<leader, Committed, Acks, LeaderConflict, Pending, UseFast, PidKeys>>

LeaderChange(l) ==
  /\ l \in R
  /\ LET old == leader IN
     LET V == CHOOSE S \in SUBSET R : Cardinality(S) >= QuorumN IN
     LET cnt(p) == Cardinality({ rr \in V : p \in SpecPool[rr] }) IN
     LET recovered == { p \in PID :
                          p \notin Committed
                          /\ cnt(p) >= RecoverQuorumN
                      } IN
     /\ leader' = l
     /\ SpecPool' =
         IF old \in R /\ old # l THEN
           [SpecPool EXCEPT ![l] = @ \cup recovered, ![old] = {}]
         ELSE
           [SpecPool EXCEPT ![l] = @ \cup recovered]
     /\ UCP' =
         IF old \in R /\ old # l THEN
           [UCP EXCEPT ![l] = @ \cup recovered, ![old] = {}]
         ELSE
           [UCP EXCEPT ![l] = @ \cup recovered]
     /\ UNCHANGED <<Committed, Acks, LeaderConflict, Pending, UseFast, PidKeys, ClientResp>>

Next ==
  \/ \E pid \in PID, c \in CMDS, uf \in BOOLEAN: Propose(pid, c, uf)
  \/ \E pid \in PID, r \in R: ProcessProposeLeader(r, pid)
  \/ \E pid \in PID, r \in R: ProcessProposeNonLeader(r, pid)
  \/ \E pid \in PID: DecideFast(pid)
  \/ \E pid \in PID: Commit(pid)
  \/ \E pid \in PID, r \in R: ProcessCommitMsg(r, pid)
  \/ \E l \in R: LeaderChange(l)

Spec == Init /\ [][Next]_vars

====