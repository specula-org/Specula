---- MODULE curp ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS REPLICAS, CMDS

Key(c) == c.key
Fast(c) == c.fast

N == Cardinality(REPLICAS)

Quorum(n) == (n \div 2) + 1
RecoverQuorum(n) == (Quorum(n) \div 2) + 1
SuperQuorum(n) == (n - Quorum(n)) + RecoverQuorum(n)

VARIABLES
    leader,
    SpecPool,
    Uncommitted,
    Proposed,
    AcceptNoConflict,
    LeaderConflict,
    FastResp,
    Committed,
    Delivered

Init ==
    /\ leader \in REPLICAS
    /\ SpecPool \in [REPLICAS -> SUBSET CMDS]
    /\ SpecPool = [r \in REPLICAS |-> {}]
    /\ Uncommitted \in [REPLICAS -> SUBSET CMDS]
    /\ Uncommitted = [r \in REPLICAS |-> {}]
    /\ Proposed = {}
    /\ AcceptNoConflict \in [CMDS -> SUBSET REPLICAS]
    /\ AcceptNoConflict = [c \in CMDS |-> {}]
    /\ LeaderConflict \in [CMDS -> BOOLEAN]
    /\ LeaderConflict = [c \in CMDS |-> FALSE]
    /\ FastResp = {}
    /\ Committed = {}
    /\ Delivered = {}

Propose(c) ==
    /\ c \in CMDS
    /\ c \notin Proposed
    /\ Proposed' = Proposed \cup {c}
    /\ UNCHANGED << leader, SpecPool, Uncommitted, AcceptNoConflict, LeaderConflict, FastResp, Committed, Delivered >>

ProcessProposeLeader(r, c) ==
    /\ c \in Proposed
    /\ leader \in REPLICAS
    /\ r = leader
    /\ c \notin SpecPool[r] \/ c \notin Uncommitted[r]
    /\ LET S == SpecPool[r] \cup Uncommitted[r] IN
       LET conflictVal == \E d \in S: d # c /\ Key(d) = Key(c) IN
       /\ SpecPool' = [SpecPool EXCEPT ![r] = @ \cup {c}]
       /\ Uncommitted' = [Uncommitted EXCEPT ![r] = @ \cup {c}]
       /\ LeaderConflict' = [LeaderConflict EXCEPT ![c] = @ \/ conflictVal]
       /\ UNCHANGED << leader, Proposed, AcceptNoConflict, FastResp, Committed, Delivered >>

ProcessProposeNonLeader(r, c) ==
    /\ c \in Proposed
    /\ leader \in REPLICAS
    /\ r \in REPLICAS \ {leader}
    /\ c \notin SpecPool[r]
    /\ LET S == SpecPool[r] IN
       LET conflictNL == \E d \in S: d # c /\ Key(d) = Key(c) IN
       /\ SpecPool' = [SpecPool EXCEPT ![r] = @ \cup {c}]
       /\ AcceptNoConflict' = [AcceptNoConflict EXCEPT ![c] = @ \cup (IF conflictNL THEN {} ELSE {r})]
       /\ UNCHANGED << leader, Uncommitted, Proposed, LeaderConflict, FastResp, Committed, Delivered >>

ClientFastResp(c) ==
    /\ c \in Proposed
    /\ Fast(c)
    /\ leader \in REPLICAS
    /\ ~LeaderConflict[c]
    /\ Cardinality(AcceptNoConflict[c]) \geq (SuperQuorum(N) - 1)
    /\ c \notin FastResp
    /\ FastResp' = FastResp \cup {c}
    /\ UNCHANGED << leader, SpecPool, Uncommitted, Proposed, AcceptNoConflict, LeaderConflict, Committed, Delivered >>

Commit(c) ==
    /\ c \notin Committed
    /\ \E r \in REPLICAS: c \in Uncommitted[r]
    /\ Committed' = Committed \cup {c}
    /\ UNCHANGED << leader, SpecPool, Uncommitted, Proposed, AcceptNoConflict, LeaderConflict, FastResp, Delivered >>

ProcessCommitMsg(r, c) ==
    /\ r \in REPLICAS
    /\ c \in Committed
    /\ SpecPool' = [SpecPool EXCEPT ![r] = @ \ {c}]
    /\ Uncommitted' = [Uncommitted EXCEPT ![r] = @ \ {c}]
    /\ UNCHANGED << leader, Proposed, AcceptNoConflict, LeaderConflict, FastResp, Committed, Delivered >>

DeliverAfterCommit(c) ==
    /\ c \in Committed
    /\ c \in Proposed
    /\ c \notin Delivered
    /\ Delivered' = Delivered \cup {c}
    /\ UNCHANGED << leader, SpecPool, Uncommitted, Proposed, AcceptNoConflict, LeaderConflict, FastResp, Committed >>

LeaderChange(l) ==
    /\ l \in REPLICAS
    /\ LET Rcv == { c \in CMDS :
                     c \notin Committed /\
                     Cardinality({ r \in REPLICAS : c \in SpecPool[r] }) \geq RecoverQuorum(N) } IN
       /\ leader' = l
       /\ Uncommitted' = [Uncommitted EXCEPT ![l] = @ \cup Rcv]
       /\ SpecPool' = [SpecPool EXCEPT ![l] = @ \cup Rcv]
       /\ UNCHANGED << Proposed, AcceptNoConflict, LeaderConflict, FastResp, Committed, Delivered >>

Next ==
    \E c \in CMDS: Propose(c)
    \/ \E r \in REPLICAS, c \in CMDS: ProcessProposeLeader(r, c)
    \/ \E r \in REPLICAS, c \in CMDS: ProcessProposeNonLeader(r, c)
    \/ \E c \in CMDS: ClientFastResp(c)
    \/ \E c \in CMDS: Commit(c)
    \/ \E r \in REPLICAS, c \in CMDS: ProcessCommitMsg(r, c)
    \/ \E c \in CMDS: DeliverAfterCommit(c)
    \/ \E l \in REPLICAS: LeaderChange(l)

Vars == << leader, SpecPool, Uncommitted, Proposed, AcceptNoConflict, LeaderConflict, FastResp, Committed, Delivered >>

Spec == Init /\ [][Next]_Vars
====