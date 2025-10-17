---- MODULE curp ----
EXTENDS TLC, Sequences, Naturals, FiniteSets

CONSTANTS
    Replicas, \* set of replica ids
    Voters,   \* subset of Replicas used for quorum calculations
    Cmds,     \* set of client command identifiers
    Key,      \* set of data keys
    Keys      \* function from Cmds to SUBSET Key: [Cmds -> SUBSET Key]

VARIABLES
    Leader,     \* current leader or Nil
    SP,         \* speculative pools: [Replicas -> SUBSET Cmds]
    UCP,        \* uncommitted pools: [Replicas -> SUBSET Cmds]
    Committed,  \* set of committed commands
    Applied,    \* applied commands per replica: [Replicas -> SUBSET Cmds]
    Pending,    \* pending client proposals: SUBSET Cmds
    Resp,       \* client-visible response state: [Cmds -> {"None","Spec","Final"}]
    UseFast,    \* per-command client choice to use fast path: [Cmds -> BOOLEAN]
    LConf       \* per-command conflict flag computed by leader processing: [Cmds -> BOOLEAN]

vars == << Leader, SP, UCP, Committed, Applied, Pending, Resp, UseFast, LConf >>

Quorum(n) == (n \div 2) + 1
RecoverQuorum(n) == (Quorum(n) \div 2) + 1
SuperQuorum(n) == (n - Quorum(n)) + RecoverQuorum(n)

NVoters == Cardinality(Voters)
QuorumSize == Quorum(NVoters)
RecoverQuorumSize == RecoverQuorum(NVoters)
SuperQuorumSize == SuperQuorum(NVoters)

KeysOf(c) == Keys[c]

Conflict(c, d) == (KeysOf(c) \cap KeysOf(d)) /= {}

ConflictsWithSet(c, S) == \E d \in S \ {c} : Conflict(c, d)

NoConflictAt(r, c) == ~ConflictsWithSet(c, SP[r])

EnoughNonConflictAcks(c) ==
    \E S \in SUBSET Voters :
        /\ Cardinality(S) >= SuperQuorumSize
        /\ Leader \in S
        /\ \A r \in S : NoConflictAt(r, c)

Init ==
    /\ Leader = Nil
    /\ SP \in [Replicas -> SUBSET Cmds]
    /\ \A r \in Replicas : SP[r] = {}
    /\ UCP \in [Replicas -> SUBSET Cmds]
    /\ \A r \in Replicas : UCP[r] = {}
    /\ Committed = {}
    /\ Applied \in [Replicas -> SUBSET Cmds]
    /\ \A r \in Replicas : Applied[r] = {}
    /\ Pending = {}
    /\ Resp \in [Cmds -> {"None","Spec","Final"}]
    /\ \A c \in Cmds : Resp[c] = "None"
    /\ UseFast \in [Cmds -> BOOLEAN]
    /\ \A c \in Cmds : UseFast[c] = FALSE
    /\ LConf \in [Cmds -> BOOLEAN]
    /\ \A c \in Cmds : LConf[c] = FALSE

Propose(c, ufp) ==
    \/ /\ c \in Cmds
       /\ c \notin Pending
       /\ Pending' = Pending \cup {c}
       /\ UseFast' = [UseFast EXCEPT ![c] = ufp]
       /\ UNCHANGED << Leader, SP, UCP, Committed, Applied, Resp, LConf >>
    \/ /\ c \in Pending
       /\ UseFast[c]
       /\ Leader \in Replicas
       /\ Resp[c] = "None"
       /\ ~LConf[c]
       /\ EnoughNonConflictAcks(c)
       /\ Resp' = [Resp EXCEPT ![c] = "Spec"]
       /\ UNCHANGED << Leader, SP, UCP, Committed, Applied, Pending, UseFast, LConf >>

ProcessProposeLeader(r, c) ==
    /\ Leader \in Replicas
    /\ r = Leader
    /\ c \in Pending
    /\ c \notin UCP[r]
    /\ LET conf == ConflictsWithSet(c, SP[r]) \/ ConflictsWithSet(c, UCP[r]) IN
       /\ SP'  = [SP  EXCEPT ![r] = @ \cup {c}]
       /\ UCP' = [UCP EXCEPT ![r] = @ \cup {c}]
       /\ LConf' = [LConf EXCEPT ![c] = conf]
       /\ UNCHANGED << Leader, Committed, Applied, Pending, Resp, UseFast >>

ProcessProposeNonLeader(r, c) ==
    /\ Leader \in Replicas
    /\ r \in Replicas \ {Leader}
    /\ c \in Pending
    /\ c \notin SP[r]
    /\ SP' = [SP EXCEPT ![r] = @ \cup {c}]
    /\ UNCHANGED << Leader, UCP, Committed, Applied, Pending, Resp, UseFast, LConf >>

Commit ==
    /\ Leader \in Replicas
    /\ \E c \in UCP[Leader] \ Committed :
        /\ Committed' = Committed \cup {c}
        /\ UNCHANGED << Leader, SP, UCP, Applied, Pending, Resp, UseFast, LConf >>

ProcessCommitMsg(r, c) ==
    /\ r \in Replicas
    /\ c \in Committed
    /\ c \notin Applied[r]
    /\ Applied' = [Applied EXCEPT ![r] = @ \cup {c}]
    /\ SP' = [SP EXCEPT ![r] = @ \ {c}]
    /\ UCP' = [UCP EXCEPT ![r] = @ \ {c}]
    /\ Resp' = [Resp EXCEPT ![c] = "Final"]
    /\ Pending' = Pending \ {c}
    /\ UNCHANGED << Leader, Committed, UseFast, LConf >>

LeaderChange(l) ==
    /\ l \in Voters
    /\ \E S \in SUBSET Voters :
        /\ Cardinality(S) >= QuorumSize
        /\ LET R == { c \in Cmds : Cardinality({ r \in S : c \in SP[r] }) >= RecoverQuorumSize } \ (Committed \cup UCP[l]) IN
           /\ Leader' = l
           /\ UCP' = [UCP EXCEPT ![l] = @ \cup R]
           /\ SP'  = [SP  EXCEPT ![l] = @ \cup R]
           /\ UNCHANGED << Committed, Applied, Pending, Resp, UseFast, LConf >>

Next ==
    \/ \E c \in Cmds, ufp \in BOOLEAN : Propose(c, ufp)
    \/ \E r \in Replicas, c \in Cmds : ProcessProposeLeader(r, c)
    \/ \E r \in Replicas, c \in Cmds : ProcessProposeNonLeader(r, c)
    \/ Commit
    \/ \E r \in Replicas, c \in Cmds : ProcessCommitMsg(r, c)
    \/ \E l \in Voters : LeaderChange(l)

Spec == Init /\ [][Next]_vars

====