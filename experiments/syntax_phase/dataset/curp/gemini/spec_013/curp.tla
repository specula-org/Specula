---- MODULE curp ----
EXTENDS TLC, Naturals, FiniteSets

CONSTANTS Replica, K, V, CId

ASSUME IsFiniteSet(Replica)
ASSUME IsFiniteSet(K)
ASSUME IsFiniteSet(V)
ASSUME IsFiniteSet(CId)

Command == [key: K, val: V, id: CId]

Quorum(S) == Cardinality(S) \div 2 + 1
FaultTolerance(S) == Cardinality(S) - Quorum(S)
RecoverQuorum(S) == Quorum(S) \div 2 + 1
SuperQuorum(S) == FaultTolerance(S) + RecoverQuorum(S)

Conflict(cmd1, cmd2) == cmd1.key = cmd2.key
ConflictsWithSet(cmd, cmdSet) == \E c \in cmdSet : Conflict(cmd, c)

VARIABLES
    leader,
    specPools,
    uncommittedPool,
    committed,
    pendingProposals,
    processedProposals

vars == <<leader, specPools, uncommittedPool, committed, pendingProposals, processedProposals>>

Init ==
    /\ leader \in Replica
    /\ specPools = [r \in Replica |-> {}]
    /\ uncommittedPool = {}
    /\ committed = {}
    /\ pendingProposals = {}
    /\ processedProposals = [r \in Replica |-> {}]

ClientPropose(cmd) ==
    /\ cmd \in Command
    /\ cmd \notin pendingProposals
    /\ cmd \notin committed
    /\ pendingProposals' = pendingProposals \cup {cmd}
    /\ UNCHANGED <<leader, specPools, uncommittedPool, committed, processedProposals>>

ProcessProposal(r, cmd) ==
    /\ r \in Replica
    /\ cmd \in pendingProposals
    /\ cmd \notin processedProposals[r]
    /\ LET
        isLeader == (r = leader)
        leaderConflictSet == IF isLeader THEN uncommittedPool ELSE {}
        hasConflict == ConflictsWithSet(cmd, specPools[r] \cup leaderConflictSet)
       IN
        /\ IF ~hasConflict THEN
            /\ specPools' = [specPools EXCEPT ![r] = @ \cup {cmd}]
            /\ uncommittedPool' = IF isLeader THEN uncommittedPool \cup {cmd} ELSE uncommittedPool
           ELSE
            /\ UNCHANGED <<specPools, uncommittedPool>>
        /\ processedProposals' = [processedProposals EXCEPT ![r] = @ \cup {cmd}]
    /\ UNCHANGED <<leader, committed, pendingProposals>>

Commit(cmd) ==
    /\ cmd \in uncommittedPool
    /\ committed' = committed \cup {cmd}
    /\ uncommittedPool' = uncommittedPool \setminus {cmd}
    /\ UNCHANGED <<leader, specPools, pendingProposals, processedProposals>>

ProcessCommitMsg(r, cmd) ==
    /\ r \in Replica
    /\ cmd \in committed
    /\ cmd \in specPools[r]
    /\ specPools' = [specPools EXCEPT ![r] = @ \setminus {cmd}]
    /\ UNCHANGED <<leader, uncommittedPool, committed, pendingProposals, processedProposals>>

LeaderChange(l, R_quorum) ==
    /\ l \in Replica
    /\ l /= leader
    /\ R_quorum \subseteq Replica
    /\ Cardinality(R_quorum) >= Quorum(Replica)
    /\ leader' = l
    /\ LET
        collectedCmds == UNION {specPools[r] : r \in R_quorum}
        cmdCounts == [c \in collectedCmds |-> Cardinality({r \in R_quorum : c \in specPools[r]})]
        recoveredCmds == {c \in DOMAIN cmdCounts : cmdCounts[c] >= RecoverQuorum(Replica)}
       IN
        /\ uncommittedPool' = recoveredCmds \setminus committed
        /\ specPools' = [specPools EXCEPT ![l] = specPools[l] \cup uncommittedPool']
    /\ UNCHANGED <<committed, pendingProposals, processedProposals>>

Next ==
    \/ \E cmd \in Command : ClientPropose(cmd)
    \/ \E r \in Replica, cmd \in pendingProposals : ProcessProposal(r, cmd)
    \/ \E cmd \in uncommittedPool : Commit(cmd)
    \/ \E r \in Replica, cmd \in committed : ProcessCommitMsg(r, cmd)
    \/ \E l \in Replica, R_quorum \subseteq Replica : LeaderChange(l, R_quorum)

Spec == Init /\ [][Next]_vars

====