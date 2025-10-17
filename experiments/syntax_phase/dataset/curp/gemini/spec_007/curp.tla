---- MODULE curp ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS
    Replicas,
    Keys,
    Values,
    Nil

ASSUME
    /\ Replicas \subseteq {"r1", "r2", "r3"}
    /\ Keys \subseteq {"k1", "k2"}
    /\ Values \subseteq {"v1", "v2"}
    /\ Nil \notin Replicas

Commands == [key: Keys, val: Values]
Roles == {"Follower", "Leader"}

VARIABLES
    term,
    role,
    leader,
    log,
    speculativePool,
    uncommittedPool,
    committedLog,
    lastApplied,
    pendingProposals

vars == <<term, role, leader, log, speculativePool, uncommittedPool, committedLog, lastApplied, pendingProposals>>

-----------------------------------------------------------------------------
\* Helper operators

Quorum(S) == Cardinality(S) \div 2 + 1

RecoverQuorum(S) == Quorum(S) \div 2 + 1

SuperQuorum(S) == (Cardinality(S) - Quorum(S)) + RecoverQuorum(S)

Conflicts(cmd1, cmd2) == cmd1["key"] = cmd2["key"]

AsSet(seq) == {seq[i] : i \in 1..Len(seq)}

BagUnion(bagOfBags) ==
    LET allKeys == UNION {DOMAIN b : b \in bagOfBags}
    IN [k \in allKeys |-> Sum({IF k \in DOMAIN b THEN b[k] ELSE 0 : b \in bagOfBags})]

-----------------------------------------------------------------------------
\* System initialization

Init ==
    /\ term = [r \in Replicas |-> 0]
    /\ role = [r \in Replicas |-> "Follower"]
    /\ leader = Nil
    /\ log = [r \in Replicas |-> <<>>]
    /\ speculativePool = [r \in Replicas |-> {}]
    /\ uncommittedPool = [r \in Replicas |-> {}]
    /\ committedLog = <<>>
    /\ lastApplied = [r \in Replicas |-> 0]
    /\ pendingProposals = [r \in Replicas |-> {}]

-----------------------------------------------------------------------------
\* Core Actions

Propose(cmd) ==
    /\ cmd \in Commands
    /\ pendingProposals' = [r \in Replicas |-> pendingProposals[r] \cup {cmd}]
    /\ UNCHANGED <<term, role, leader, log, speculativePool, uncommittedPool, committedLog, lastApplied>>

ProcessProposeLeader(r, cmd) ==
    /\ r \in Replicas
    /\ cmd \in pendingProposals[r]
    /\ role[r] = "Leader"
    /\ (LET hasConflict == \E c \in speculativePool[r] \cup uncommittedPool[r] : Conflicts(c, cmd)
       IN /\ speculativePool' = [speculativePool EXCEPT ![r] = (@ \cup {cmd})]
          /\ IF hasConflict THEN
                UNCHANGED <<log, uncommittedPool>>
             ELSE
                /\ log' = [log EXCEPT ![r] = Append(@, cmd)]
                /\ uncommittedPool' = [uncommittedPool EXCEPT ![r] = (@ \cup {cmd})]
          /\ pendingProposals' = [pendingProposals EXCEPT ![r] = (@ \setminus {cmd})])
    /\ UNCHANGED <<term, role, leader, committedLog, lastApplied>>

ProcessProposeNonLeader(r, cmd) ==
    /\ r \in Replicas
    /\ cmd \in pendingProposals[r]
    /\ role[r] = "Follower"
    /\ speculativePool' = [speculativePool EXCEPT ![r] = (@ \cup {cmd})]
    /\ pendingProposals' = [pendingProposals EXCEPT ![r] = (@ \setminus {cmd})]
    /\ UNCHANGED <<term, role, leader, log, uncommittedPool, committedLog, lastApplied>>

Commit(l, cmd) ==
    /\ l \in Replicas
    /\ role[l] = "Leader"
    /\ cmd \in uncommittedPool[l]
    /\ cmd \notin AsSet(committedLog)
    /\ LET idx == CHOOSE i \in 1..Len(log[l]) : log[l][i] = cmd
       IN /\ Cardinality({r \in Replicas : Len(log[r]) >= idx /\ log[r][idx] = cmd}) >= Quorum(Replicas)
          /\ \A i \in 1..(idx-1) : log[l][i] \in AsSet(committedLog)
    /\ committedLog' = Append(committedLog, cmd)
    /\ UNCHANGED <<term, role, leader, log, speculativePool, uncommittedPool, lastApplied, pendingProposals>>

ProcessCommitMsg(r) ==
    /\ r \in Replicas
    /\ Len(committedLog) > lastApplied[r]
    /\ LET cmdToApply == committedLog[lastApplied[r] + 1]
       IN /\ speculativePool' = [speculativePool EXCEPT ![r] = (@ \setminus {cmdToApply})]
          /\ uncommittedPool' = [uncommittedPool EXCEPT ![r] = (@ \setminus {cmdToApply})]
          /\ lastApplied' = [lastApplied EXCEPT ![r] = (@ + 1)]
    /\ UNCHANGED <<term, role, leader, log, committedLog, pendingProposals>>

LeaderChange(l) ==
    /\ l \in Replicas
    /\ LET newTerm == 1 + IF Replicas = {} THEN 0 ELSE Max({term[r] : r \in Replicas})
       IN /\ \E S \subseteq Replicas:
             /\ Cardinality(S) >= RecoverQuorum(Replicas)
             /\ LET collectedPoolsBag == BagUnion({Bagify(speculativePool[r]) : r \in S})
                recoveredCmdsSet == {c \in DOMAIN collectedPoolsBag : collectedPoolsBag[c] >= RecoverQuorum(Replicas)}
                IN \E recoveredCmdsSeq \in Permutations(recoveredCmdsSet):
                      LET newLogL == log[l] \o recoveredCmdsSeq
                          committedInLog == AsSet(SubSeq(committedLog, 1, lastApplied[l]))
                          newUncommittedPoolL == AsSet(newLogL) \setminus committedInLog
                      IN /\ term' = [r \in Replicas |-> newTerm]
                         /\ role' = [r \in Replicas |-> IF r = l THEN "Leader" ELSE "Follower"]
                         /\ leader' = l
                         /\ log' = [log EXCEPT ![l] = newLogL]
                         /\ uncommittedPool' = [r \in Replicas |-> IF r = l THEN newUncommittedPoolL ELSE {}]
                         /\ speculativePool' = [r \in Replicas |-> IF r = l THEN newUncommittedPoolL ELSE speculativePool[r]]
    /\ UNCHANGED <<committedLog, lastApplied, pendingProposals>>

-----------------------------------------------------------------------------
\* Definition of the next-state relation

Next ==
    \/ \E c \in Commands : Propose(c)
    \/ \E r \in Replicas : \E cmd \in pendingProposals[r] : ProcessProposeLeader(r, cmd)
    \/ \E r \in Replicas : \E cmd \in pendingProposals[r] : ProcessProposeNonLeader(r, cmd)
    \/ \E l \in Replicas : \E cmd \in uncommittedPool[l] : Commit(l, cmd)
    \/ \E r \in Replicas : ProcessCommitMsg(r)
    \/ \E l \in Replicas : LeaderChange(l)

Spec == Init /\ [][Next]_vars

====