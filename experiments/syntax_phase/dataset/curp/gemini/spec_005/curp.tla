---- MODULE curp ----
EXTENDS Naturals, Sequences, FiniteSets, TLC, SequencesExt, Bags

CONSTANTS
    Replicas,
    cmd1,
    cmd2,
    cmd3,
    Nil

Commands == {cmd1, cmd2, cmd3}

CommandKeys(cmd) == CASE cmd = cmd1 -> {"k1"}
                     [] cmd = cmd2 -> {"k2"}
                     [] cmd = cmd3 -> {"k1"}

VARIABLES
    term,
    role,
    log,
    commitIndex,
    speculativePool,
    uncommittedPool,
    pendingProposals

vars == <<term, role, log, commitIndex, speculativePool, uncommittedPool, pendingProposals>>

QuorumSize == (Cardinality(Replicas) \div 2) + 1
RecoverQuorumSize == (QuorumSize \div 2) + 1

LogEntry == [cmd: Commands, term: Naturals]

Init ==
    /\ term = [r \in Replicas |-> 0]
    /\ role = [r \in Replicas |-> "Follower"]
    /\ log = [r \in Replicas |-> << >>]
    /\ commitIndex = [r \in Replicas |-> 0]
    /\ speculativePool = [r \in Replicas |-> {}]
    /\ uncommittedPool = [r \in Replicas |-> {}]
    /\ pendingProposals = {}

Propose(cmd) ==
    /\ cmd \in Commands
    /\ pendingProposals' = pendingProposals \cup {cmd}
    /\ UNCHANGED <<term, role, log, commitIndex, speculativePool, uncommittedPool>>

ProcessProposeLeader(r, cmd) ==
    /\ role[r] = "Leader"
    /\ LET keys(c) == CommandKeys(c)
          specKeys == UNION {keys(c) : c \in speculativePool[r]}
          uncommittedKeys == UNION {keys(c) : c \in uncommittedPool[r]}
          isConflict == (keys(cmd) \cap specKeys /= {}) \/ (keys(cmd) \cap uncommittedKeys /= {})
       IN /\ log' = [log EXCEPT ![r] = Append(@, [cmd |-> cmd, term |-> term[r]])]
          /\ uncommittedPool' = [uncommittedPool EXCEPT ![r] = @ \cup {cmd}]
          /\ IF \lnot isConflict
             THEN speculativePool' = [speculativePool EXCEPT ![r] = @ \cup {cmd}]
             ELSE UNCHANGED speculativePool
          /\ UNCHANGED <<term, role, commitIndex, pendingProposals>>

ProcessProposeNonLeader(r, cmd) ==
    /\ role[r] = "Follower"
    /\ LET keys(c) == CommandKeys(c)
          specKeys == UNION {keys(c) : c \in speculativePool[r]}
          isConflict == keys(cmd) \cap specKeys /= {}
       IN /\ IF \lnot isConflict
             THEN speculativePool' = [speculativePool EXCEPT ![r] = @ \cup {cmd}]
             ELSE UNCHANGED speculativePool
          /\ UNCHANGED <<term, role, log, commitIndex, uncommittedPool, pendingProposals>>

ProcessPropose(r, cmd) ==
    /\ cmd \in pendingProposals
    /\ IF role[r] = "Leader"
       THEN ProcessProposeLeader(r, cmd)
       ELSE ProcessProposeNonLeader(r, cmd)
    /\ pendingProposals' = pendingProposals \ {cmd}

Commit ==
    /\ \E leader \in Replicas:
        /\ role[leader] = "Leader"
        /\ \E idx \in (commitIndex[leader] + 1)..Len(log[leader]):
            /\ commitIndex' = [commitIndex EXCEPT ![leader] = idx]
            /\ UNCHANGED <<term, role, log, speculativePool, uncommittedPool, pendingProposals>>

ProcessCommitMsg(r) ==
    /\ \E leader \in Replicas:
        /\ role[leader] = "Leader"
        /\ \E newCI \in (commitIndex[r] + 1)..Min({Len(log[r]), commitIndex[leader]}):
            LET committedCmds == {log[r][i]["cmd"] : i \in (commitIndex[r] + 1)..newCI}
            IN /\ commitIndex' = [commitIndex EXCEPT ![r] = newCI]
               /\ speculativePool' = [speculativePool EXCEPT ![r] = @ \ committedCmds]
               /\ uncommittedPool' = [uncommittedPool EXCEPT ![r] = @ \ committedCmds]
               /\ UNCHANGED <<term, role, log, pendingProposals>>

LeaderChange(newLeader) ==
    /\ LET maxTerm == IF Replicas = {} THEN 0 ELSE CHOOSE v \in {term[r] : r \in Replicas} : \A r2 \in Replicas : v >= term[r2] IN
       \E newTerm \in {maxTerm + 1}:
        /\ \E voters \subseteq Replicas:
            /\ Cardinality(voters) >= QuorumSize
            /\ LET
                AllPoolsAsBags == [v \in voters |-> ToBag(speculativePool[v])]
                UnionBag == BagUnion({AllPoolsAsBags[v] : v \in DOMAIN AllPoolsAsBags})
                RecoveredCmds == {c \in DOMAIN UnionBag : UnionBag[c] >= RecoverQuorumSize}
                ExistingCmdsInLog == {e["cmd"] : e \in log[newLeader]}
                CmdsToLog == RecoveredCmds \ ExistingCmdsInLog
               IN \E newEntries \in [1..Cardinality(CmdsToLog) -> LogEntry]:
                    /\ {newEntries[e]["cmd"] : e \in DOMAIN newEntries} = CmdsToLog
                    /\ \A i \in DOMAIN newEntries: newEntries[i]["term"] = newTerm
                    /\ LET newLog == log[newLeader] \o Seq(newEntries)
                           newSpecPool == speculativePool[newLeader] \cup RecoveredCmds
                           newUncommittedPool == {e["cmd"] : i \in (commitIndex[newLeader] + 1)..Len(newLog), LET e == newLog[i]}
                    IN /\ term' = [r \in Replicas |-> newTerm]
                       /\ role' = [r \in Replicas |-> IF r = newLeader THEN "Leader" ELSE "Follower"]
                       /\ log' = [log EXCEPT ![newLeader] = newLog]
                       /\ speculativePool' = [speculativePool EXCEPT ![newLeader] = newSpecPool]
                       /\ uncommittedPool' = [u \in Replicas |-> IF u = newLeader THEN newUncommittedPool ELSE {}]
                       /\ UNCHANGED <<commitIndex, pendingProposals>>

Next ==
    \/ \E cmd \in Commands : Propose(cmd)
    \/ \E r \in Replicas, cmd \in pendingProposals : ProcessPropose(r, cmd)
    \/ Commit
    \/ \E r \in Replicas : ProcessCommitMsg(r)
    \/ \E newLeader \in Replicas : LeaderChange(newLeader)

Spec == Init /\ [][Next]_vars

====