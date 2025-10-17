---- MODULE curp ----
EXTENDS TLC, Sequences, Naturals, FiniteSets, Bags

CONSTANTS Replicas, Commands, Keys, InitialLeader

ASSUME \A c \in Commands: c.key \in Keys
ASSUME InitialLeader \in Replicas

VARIABLES
    role,
    term,
    log,
    speculativePool,
    uncommittedPool,
    commitIndex,
    lastApplied,
    pendingProposals,
    replicaResponses

vars == <<role, term, log, speculativePool, uncommittedPool, commitIndex, lastApplied, pendingProposals, replicaResponses>>

\* --- Operators ---

RECURSIVE SetToSeq
SetToSeq(S) == CHOOSE s \in [1..Cardinality(S) -> S] :
    \A i, j \in DOMAIN s: i # j => s[i] # s[j]

Conflicts(cmd1, cmd2) == cmd1.key = cmd2.key

QuorumSize == (Cardinality(Replicas) \div 2) + 1

RecoverQuorumSize == (QuorumSize \div 2) + 1

SuperQuorumSize == (Cardinality(Replicas) - QuorumSize) + RecoverQuorumSize

IsMoreUpToDate(r1, r2) ==
    LET r1Term == term[r1]
        r2Term == term[r2]
        r1LogLen == Len(log[r1])
        r2LogLen == Len(log[r2])
    IN \/ r1Term > r2Term
       \/ (r1Term = r2Term /\ r1LogLen >= r2LogLen)

\* --- Initial State ---

Init ==
    /\ role = [r \in Replicas |-> IF r = InitialLeader THEN "Leader" ELSE "Follower"]
    /\ term = [r \in Replicas |-> 1]
    /\ log = [r \in Replicas |-> <<>>]
    /\ speculativePool = [r \in Replicas |-> {}]
    /\ uncommittedPool = [r \in Replicas |-> {}]
    /\ commitIndex = [r \in Replicas |-> 0]
    /\ lastApplied = [r \in Replicas |-> 0]
    /\ pendingProposals = [r \in Replicas |-> {}]
    /\ replicaResponses = [cmd \in Commands |-> {}]

\* --- Actions ---

Propose(cmd) ==
    /\ pendingProposals' = [r \in Replicas |-> pendingProposals[r] \cup {cmd}]
    /\ replicaResponses' = [replicaResponses EXCEPT ![cmd] = {}]
    /\ UNCHANGED <<role, term, log, speculativePool, uncommittedPool, commitIndex, lastApplied>>

ProcessProposeLeader(r, cmd) ==
    /\ cmd \in pendingProposals[r]
    /\ role[r] = "Leader"
    /\ LET conflictsWithSpec     == \E c \in speculativePool[r] : Conflicts(c, cmd)
           conflictsWithUncommit == \E c \in uncommittedPool[r] : Conflicts(c, cmd)
       IN IF ~conflictsWithSpec /\ ~conflictsWithUncommit
          THEN /\ speculativePool' = [speculativePool EXCEPT ![r] = @ \cup {cmd}]
               /\ uncommittedPool' = [uncommittedPool EXCEPT ![r] = @ \cup {cmd}]
               /\ log' = [log EXCEPT ![r] = Append(@, cmd)]
               /\ replicaResponses' = [replicaResponses EXCEPT ![cmd] = @ \cup {r}]
          ELSE /\ UNCHANGED <<speculativePool, uncommittedPool, log, replicaResponses>>
    /\ pendingProposals' = [pendingProposals EXCEPT ![r] = @ \ {cmd}]
    /\ UNCHANGED <<role, term, commitIndex, lastApplied>>

ProcessProposeNonLeader(r, cmd) ==
    /\ cmd \in pendingProposals[r]
    /\ role[r] # "Leader"
    /\ LET conflictsWithSpec == \E c \in speculativePool[r] : Conflicts(c, cmd)
       IN IF ~conflictsWithSpec
          THEN /\ speculativePool' = [speculativePool EXCEPT ![r] = @ \cup {cmd}]
               /\ replicaResponses' = [replicaResponses EXCEPT ![cmd] = @ \cup {r}]
               /\ UNCHANGED <<uncommittedPool, log>>
          ELSE /\ UNCHANGED <<speculativePool, uncommittedPool, log, replicaResponses>>
    /\ pendingProposals' = [pendingProposals EXCEPT ![r] = @ \ {cmd}]
    /\ UNCHANGED <<role, term, commitIndex, lastApplied>>

Commit(l, i) ==
    /\ role[l] = "Leader"
    /\ i > commitIndex[l]
    /\ LET cmdToCommit == log[l][i]
           replicasWithLog == {r \in Replicas : Len(log[r]) >= i /\ log[r][i] = cmdToCommit}
       IN Cardinality(replicasWithLog) >= QuorumSize
    /\ commitIndex' = [r \in Replicas |-> IF r \in replicasWithLog THEN i ELSE commitIndex[r]]
    /\ UNCHANGED <<role, term, log, speculativePool, uncommittedPool, lastApplied, pendingProposals, replicaResponses>>

ProcessCommitMsg(r) ==
    /\ lastApplied[r] < commitIndex[r]
    /\ LET i == lastApplied[r] + 1
           cmdToApply == log[r][i]
       IN /\ speculativePool' = [speculativePool EXCEPT ![r] = @ \ {cmdToApply}]
          /\ uncommittedPool' = [uncommittedPool EXCEPT ![r] = @ \ {cmdToApply}]
          /\ lastApplied' = [lastApplied EXCEPT ![r] = i]
    /\ UNCHANGED <<role, term, log, commitIndex, pendingProposals, replicaResponses>>

LeaderChange(newLeader, Voters) ==
    /\ Cardinality(Voters) >= QuorumSize
    /\ newLeader \in Voters
    /\ \A v \in Voters : IsMoreUpToDate(newLeader, v)
    /\ LET maxTerm == IF Voters = {} THEN 0 ELSE Max({term[v] : v \in Voters})
           newTerm == maxTerm + 1
           Sps == {speculativePool[v] : v \in Voters}
           AllCmdsBag == SeqToBag(SetToSeq(UNION Sps))
           recoveredCmds == {c \in DOMAIN AllCmdsBag : BagCount(c, AllCmdsBag) >= RecoverQuorumSize}
           logCmds == {log[newLeader][i] : i \in 1..Len(log[newLeader])}
           newCmdsToLog == recoveredCmds \ logCmds
           newCmdsSeq == SetToSeq(newCmdsToLog)
       IN /\ term' = [r \in Replicas |-> IF r \in Voters THEN newTerm ELSE term[r]]
          /\ role' = [r \in Replicas |-> IF r = newLeader THEN "Leader" ELSE "Follower"]
          /\ log' = [log EXCEPT ![newLeader] = @ \o newCmdsSeq]
          /\ speculativePool' = [speculativePool EXCEPT ![newLeader] = @ \cup newCmdsToLog]
          /\ uncommittedPool' = [uncommittedPool EXCEPT ![newLeader] = @ \cup newCmdsToLog]
    /\ UNCHANGED <<commitIndex, lastApplied, pendingProposals, replicaResponses>>

\* --- Next State ---

Next ==
    \/ \E cmd \in Commands : Propose(cmd)
    \/ \E r \in Replicas : \E cmd \in pendingProposals[r] : ProcessProposeLeader(r, cmd)
    \/ \E r \in Replicas : \E cmd \in pendingProposals[r] : ProcessProposeNonLeader(r, cmd)
    \/ \E l \in Replicas : \E i \in 1..Len(log[l]) : Commit(l, i)
    \/ \E r \in Replicas : ProcessCommitMsg(r)
    \/ \E newLeader \in Replicas : \E Voters \in SUBSET Replicas : LeaderChange(newLeader, Voters)

Spec == Init /\ [][Next]_vars

====