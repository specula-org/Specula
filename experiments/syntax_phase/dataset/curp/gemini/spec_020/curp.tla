---- MODULE curp ----
EXTENDS TLC, Sequences, Naturals, FiniteSets, Bags

CONSTANTS Replicas, Commands, Nil, Keys

ASSUME IsFiniteSet(Replicas)
ASSUME IsFiniteSet(Commands)
ASSUME Nil \notin Replicas
ASSUME \A cmd \in Commands: cmd \in [key: Keys]

VARIABLES
    term,
    leader,
    role,
    speculativePool,
    uncommittedPool,
    log,
    commitIndex,
    lastApplied,
    pendingProposals

vars == <<term, leader, role, speculativePool, uncommittedPool, log, commitIndex, lastApplied, pendingProposals>>

\* Operator to convert a set to a sequence non-deterministically.
Range(s) == {s[i] : i \in DOMAIN s}
SetToSeq(S) == CHOOSE s \in Seq(S) : Range(s) = S /\ Len(s) = Cardinality(S)

Max(a, b) == IF a >= b THEN a ELSE b

TypeOK ==
    /\ term \in Nat
    /\ leader \in Replicas \cup {Nil}
    /\ role \in [Replicas -> {"Leader", "Follower"}]
    /\ speculativePool \in [Replicas -> SUBSET Commands]
    /\ uncommittedPool \in [Replicas -> SUBSET Commands]
    /\ log \in [Replicas -> Seq(Commands)]
    /\ commitIndex \in [Replicas -> Nat]
    /\ lastApplied \in [Replicas -> Nat]
    /\ pendingProposals \in [Replicas -> SUBSET Commands]

Init ==
    /\ term = 0
    /\ leader = Nil
    /\ role = [r \in Replicas |-> "Follower"]
    /\ speculativePool = [r \in Replicas |-> {}]
    /\ uncommittedPool = [r \in Replicas |-> {}]
    /\ log = [r \in Replicas |-> <<>>]
    /\ commitIndex = [r \in Replicas |-> 0]
    /\ lastApplied = [r \in Replicas |-> 0]
    /\ pendingProposals = [r \in Replicas |-> {}]

\* Quorum definitions based on the number of replicas
QuorumSize == (Cardinality(Replicas) \div 2) + 1
RecoverQuorumSize == (QuorumSize \div 2) + 1

\* Operator to check for command conflicts based on keys
Conflicts(c1, c2) == c1["key"] = c2["key"]

\* 1. Client proposes a command to all replicas
Propose(cmd) ==
    /\ cmd \in Commands
    /\ pendingProposals' = [r \in Replicas |-> pendingProposals[r] \cup {cmd}]
    /\ UNCHANGED <<term, leader, role, speculativePool, uncommittedPool, log, commitIndex, lastApplied>>

\* 2. Leader processes a proposed command
ProcessProposeLeader(r, cmd) ==
    /\ role[r] = "Leader"
    /\ cmd \in pendingProposals[r]
    /\ LET conflict == \E c_prime \in (speculativePool[r] \cup uncommittedPool[r]) : Conflicts(cmd, c_prime)
       IN
        /\ pendingProposals' = [pendingProposals EXCEPT ![r] = pendingProposals[r] \ {cmd}]
        /\ speculativePool' = [speculativePool EXCEPT ![r] = speculativePool[r] \cup {cmd}]
        /\ IF ~conflict THEN
            /\ uncommittedPool' = [uncommittedPool EXCEPT ![r] = uncommittedPool[r] \cup {cmd}]
            /\ log' = [log EXCEPT ![r] = Append(log[r], cmd)]
           ELSE
            /\ UNCHANGED <<uncommittedPool, log>>
    /\ UNCHANGED <<term, leader, role, commitIndex, lastApplied>>

\* 3. Non-leader processes a proposed command
ProcessProposeNonLeader(r, cmd) ==
    /\ role[r] = "Follower"
    /\ cmd \in pendingProposals[r]
    /\ pendingProposals' = [pendingProposals EXCEPT ![r] = pendingProposals[r] \ {cmd}]
    /\ speculativePool' = [speculativePool EXCEPT ![r] = speculativePool[r] \cup {cmd}]
    /\ UNCHANGED <<term, leader, role, uncommittedPool, log, commitIndex, lastApplied>>

\* 4. Backend consensus protocol commits a command
Commit ==
    /\ leader /= Nil
    /\ \E i \in 1..Len(log[leader]) :
        /\ i > commitIndex[leader]
        /\ LET cmd == log[leader][i]
           IN
            /\ Cardinality({r \in Replicas : Len(log[r]) >= i /\ log[r][i] = cmd}) >= QuorumSize
            /\ commitIndex' = [r \in Replicas |-> IF Len(log[r]) >= i /\ log[r][i] = cmd THEN Max(commitIndex[r], i) ELSE commitIndex[r]]
            /\ UNCHANGED <<term, leader, role, pendingProposals, speculativePool, uncommittedPool, log, lastApplied>>

\* 5. Replica processes a committed command and applies garbage collection
ProcessCommitMsg(r, i) ==
    /\ r \in Replicas
    /\ i \in 1..Len(log[r])
    /\ i > lastApplied[r]
    /\ i <= commitIndex[r]
    /\ LET cmd == log[r][i]
       IN
        /\ lastApplied' = [lastApplied EXCEPT ![r] = i]
        /\ speculativePool' = [speculativePool EXCEPT ![r] = speculativePool[r] \ {cmd}]
        /\ uncommittedPool' = [uncommittedPool EXCEPT ![r] = uncommittedPool[r] \ {cmd}]
        /\ UNCHANGED <<term, leader, role, pendingProposals, log, commitIndex>>

\* 6. Backend protocol elects a new leader and recovers state
LeaderChange(l) ==
    /\ l \in Replicas
    /\ leader /= l
    /\ \E Q_vote \in SUBSET Replicas:
        /\ Cardinality(Q_vote) >= QuorumSize
        /\ LET
            AllSpecCmdsBag == BagUnion({SetToBag(speculativePool[r]) : r \in Q_vote})
            RecoveredCmds == { cmd \in DOMAIN AllSpecCmdsBag : AllSpecCmdsBag[cmd] >= RecoverQuorumSize }
           IN
            /\ term' = term + 1
            /\ leader' = l
            /\ role' = [r \in Replicas |-> IF r = l THEN "Leader" ELSE "Follower"]
            /\ uncommittedPool' = [uncommittedPool EXCEPT ![l] = RecoveredCmds]
            /\ speculativePool' = [speculativePool EXCEPT ![l] = RecoveredCmds]
            /\ log' = [log EXCEPT ![l] = log[l] \o SetToSeq(RecoveredCmds)]
            /\ UNCHANGED <<pendingProposals, commitIndex, lastApplied>>

Next ==
    \/ \E cmd \in Commands : Propose(cmd)
    \/ \E r \in Replicas, cmd \in pendingProposals[r] : ProcessProposeLeader(r, cmd)
    \/ \E r \in Replicas, cmd \in pendingProposals[r] : ProcessProposeNonLeader(r, cmd)
    \/ Commit
    \/ \E r \in Replicas, i \in 1..Len(log[r]) : ProcessCommitMsg(r, i)
    \/ \E l \in Replicas : LeaderChange(l)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

====