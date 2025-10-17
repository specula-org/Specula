---- MODULE curp ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS
  REPLICAS,
  KEYS,
  COMMANDS,
  Keys

N == Cardinality(REPLICAS)

Quorum(n) == (n \div 2) + 1
RecoverQuorum(n) == (Quorum(n) \div 2) + 1
SuperQuorum(n) == (n - Quorum(n)) + RecoverQuorum(n)

QuorumSize == Quorum(N)
RecoverQ == RecoverQuorum(N)
SuperQ == SuperQuorum(N)

Roles == {"Leader", "Follower"}

Conflicts(cmd, pool) ==
  \E c \in pool: (Keys[c] \cap Keys[cmd]) # {}

VARIABLES
  leader,
  role,
  SP,
  UCP,
  Committed,
  Proposed,
  UseFast,
  LeaderConflict,
  LeaderProcessed,
  RecordOK,
  ClientResponded

TypeOK ==
  /\ leader \in REPLICAS
  /\ role \in [REPLICAS -> Roles]
  /\ SP \in [REPLICAS -> SUBSET COMMANDS]
  /\ UCP \in [REPLICAS -> SUBSET COMMANDS]
  /\ Committed \subseteq COMMANDS
  /\ Proposed \subseteq COMMANDS
  /\ UseFast \in [COMMANDS -> BOOLEAN]
  /\ LeaderConflict \in [COMMANDS -> BOOLEAN]
  /\ LeaderProcessed \subseteq COMMANDS
  /\ RecordOK \in [COMMANDS -> SUBSET REPLICAS]
  /\ ClientResponded \in [COMMANDS -> BOOLEAN]
  /\ \A c \in COMMANDS: Keys[c] \subseteq KEYS

Init ==
  /\ leader \in REPLICAS
  /\ role = [r \in REPLICAS |-> IF r = leader THEN "Leader" ELSE "Follower"]
  /\ SP = [r \in REPLICAS |-> {}]
  /\ UCP = [r \in REPLICAS |-> {}]
  /\ Committed = {}
  /\ Proposed = {}
  /\ UseFast = [c \in COMMANDS |-> FALSE]
  /\ LeaderConflict = [c \in COMMANDS |-> FALSE]
  /\ LeaderProcessed = {}
  /\ RecordOK = [c \in COMMANDS |-> {}]
  /\ ClientResponded = [c \in COMMANDS |-> FALSE]
  /\ TypeOK

Followers == REPLICAS \ {leader}

Propose(cmd) ==
  /\ cmd \in COMMANDS \ Proposed
  /\ \E b \in BOOLEAN:
       /\ Proposed' = Proposed \cup {cmd}
       /\ UseFast' = [UseFast EXCEPT ![cmd] = b]
       /\ UNCHANGED << leader, role, SP, UCP, Committed, LeaderConflict, LeaderProcessed, RecordOK, ClientResponded >>
  /\ TypeOK

ProcessProposeLeader(r, cmd) ==
  /\ r = leader
  /\ role[r] = "Leader"
  /\ cmd \in Proposed
  /\ ~(cmd \in LeaderProcessed)
  /\ LET pool == SP[r] \cup UCP[r] IN
     LET conflict == Conflicts(cmd, pool) IN
       /\ SP' = [SP EXCEPT ![r] = SP[r] \cup {cmd}]
       /\ UCP' = [UCP EXCEPT ![r] = UCP[r] \cup {cmd}]
       /\ LeaderConflict' = [LeaderConflict EXCEPT ![cmd] = conflict]
       /\ LeaderProcessed' = LeaderProcessed \cup {cmd}
       /\ UNCHANGED << leader, role, Committed, Proposed, UseFast, RecordOK, ClientResponded >>
  /\ TypeOK

ProcessProposeNonLeader(r, cmd) ==
  /\ r \in Followers
  /\ role[r] = "Follower"
  /\ cmd \in Proposed
  /\ r \notin RecordOK[cmd]
  /\ LET pool == SP[r] IN
     LET conflict == Conflicts(cmd, pool) IN
       /\ SP' = [SP EXCEPT ![r] = SP[r] \cup {cmd}]
       /\ RecordOK' =
            IF ~conflict
            THEN [RecordOK EXCEPT ![cmd] = RecordOK[cmd] \cup {r}]
            ELSE RecordOK
       /\ UNCHANGED << leader, role, UCP, Committed, Proposed, UseFast, LeaderConflict, LeaderProcessed, ClientResponded >>
  /\ TypeOK

ClientFastComplete(cmd) ==
  /\ cmd \in Proposed
  /\ ~ClientResponded[cmd]
  /\ UseFast[cmd]
  /\ cmd \in LeaderProcessed
  /\ ~LeaderConflict[cmd]
  /\ Cardinality(RecordOK[cmd]) >= (SuperQ - 1)
  /\ ClientResponded' = [ClientResponded EXCEPT ![cmd] = TRUE]
  /\ UNCHANGED << leader, role, SP, UCP, Committed, Proposed, UseFast, LeaderConflict, LeaderProcessed, RecordOK >>
  /\ TypeOK

ClientSlowComplete(cmd) ==
  /\ cmd \in Proposed
  /\ ~ClientResponded[cmd]
  /\ ( ~UseFast[cmd]
      \/ LeaderConflict[cmd]
      \/ Cardinality(RecordOK[cmd]) < (SuperQ - 1)
     )
  /\ cmd \in Committed
  /\ ClientResponded' = [ClientResponded EXCEPT ![cmd] = TRUE]
  /\ UNCHANGED << leader, role, SP, UCP, Committed, Proposed, UseFast, LeaderConflict, LeaderProcessed, RecordOK >>
  /\ TypeOK

Commit ==
  /\ \E c \in (UCP[leader] \ Committed):
       /\ Committed' = Committed \cup {c}
       /\ UNCHANGED << leader, role, SP, UCP, Proposed, UseFast, LeaderConflict, LeaderProcessed, RecordOK, ClientResponded >>
  /\ TypeOK

ProcessCommitMsg(r, cmd) ==
  /\ r \in REPLICAS
  /\ cmd \in Committed
  /\ SP' = [SP EXCEPT ![r] = SP[r] \ {cmd}]
  /\ UCP' = [UCP EXCEPT ![r] = UCP[r] \ {cmd}]
  /\ UNCHANGED << leader, role, Committed, Proposed, UseFast, LeaderConflict, LeaderProcessed, RecordOK, ClientResponded >>
  /\ TypeOK

LeaderChange(l) ==
  /\ l \in REPLICAS
  /\ \E Q \in SUBSET REPLICAS:
       /\ Cardinality(Q) >= QuorumSize
       /\ LET cnt(c) == Cardinality({ r \in Q: c \in SP[r] }) IN
          LET recovered == { c \in COMMANDS: (cnt(c) >= RecoverQ) /\ ~(c \in Committed) } IN
            /\ leader' = l
            /\ role' = [r \in REPLICAS |-> IF r = l THEN "Leader" ELSE "Follower"]
            /\ UCP' = [r \in REPLICAS |-> IF r = l THEN recovered ELSE {}]
            /\ SP' = [SP EXCEPT ![l] = SP[l] \cup recovered]
            /\ LeaderProcessed' = {}
            /\ RecordOK' = [c \in COMMANDS |-> {}]
            /\ UNCHANGED << Committed, Proposed, UseFast, LeaderConflict, ClientResponded >>
  /\ TypeOK

Next ==
     \E cmd \in COMMANDS: Propose(cmd)
  \/ \E r \in REPLICAS, cmd \in COMMANDS: ProcessProposeLeader(r, cmd)
  \/ \E r \in REPLICAS, cmd \in COMMANDS: ProcessProposeNonLeader(r, cmd)
  \/ Commit
  \/ \E r \in REPLICAS, cmd \in COMMANDS: ProcessCommitMsg(r, cmd)
  \/ \E l \in REPLICAS: LeaderChange(l)
  \/ \E cmd \in COMMANDS: ClientFastComplete(cmd)
  \/ \E cmd \in COMMANDS: ClientSlowComplete(cmd)

Spec ==
  Init /\ [][Next]_<<leader, role, SP, UCP, Committed, Proposed, UseFast, LeaderConflict, LeaderProcessed, RecordOK, ClientResponded>>

====