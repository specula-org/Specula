---- MODULE curp ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS 
    Replicas,
    Commands,
    Keys

VARIABLES
    speculativePool,
    uncommittedPool,
    commitIndex,
    leaderState,
    clientResponses,
    logEntries,
    quorumStatus

vars == <<speculativePool, uncommittedPool, commitIndex, leaderState, clientResponses, logEntries, quorumStatus>>

TypeOK ==
    /\ speculativePool \in [Replicas -> SUBSET Commands]
    /\ uncommittedPool \in SUBSET Commands
    /\ commitIndex \in Nat
    /\ leaderState \in [leader: Replicas \cup {NoLeader}, term: Nat]
    /\ clientResponses \in [Commands -> {"fast", "slow", "pending"}]
    /\ logEntries \in Seq(Commands)
    /\ quorumStatus \in [Commands -> [responses: SUBSET Replicas, conflicts: SUBSET Replicas]]

NoLeader == CHOOSE x : x \notin Replicas

Quorum == Cardinality(Replicas) \div 2 + 1
SuperQuorum == (Cardinality(Replicas) - Quorum) + ((Quorum \div 2) + 1)
RecoverQuorum == (Quorum \div 2) + 1

ConflictsWith(cmd1, cmd2) ==
    \E k \in Keys : k \in cmd1.keys /\ k \in cmd2.keys

Init ==
    /\ speculativePool = [r \in Replicas |-> {}]
    /\ uncommittedPool = {}
    /\ commitIndex = 0
    /\ leaderState = [leader |-> NoLeader, term |-> 0]
    /\ clientResponses = [c \in Commands |-> "pending"]
    /\ logEntries = <<>>
    /\ quorumStatus = [c \in Commands |-> [responses |-> {}, conflicts |-> {}]]

Propose(cmd) ==
    /\ clientResponses[cmd] = "pending"
    /\ speculativePool' = [r \in Replicas |-> speculativePool[r] \cup {cmd}]
    /\ quorumStatus' = [quorumStatus EXCEPT ![cmd].responses = {}]
    /\ UNCHANGED <<uncommittedPool, commitIndex, leaderState, clientResponses, logEntries>>

ProcessProposeLeader(r, cmd) ==
    /\ leaderState.leader = r
    /\ clientResponses[cmd] = "pending"
    /\ LET specConflict == \E c \in speculativePool[r] : ConflictsWith(cmd, c)
           uncommittedConflict == \E c \in uncommittedPool : ConflictsWith(cmd, c)
           hasConflict == specConflict \/ uncommittedConflict
       IN /\ quorumStatus' = [quorumStatus EXCEPT ![cmd].responses = @ \cup {r},
                                                  ![cmd].conflicts = IF hasConflict THEN @ \cup {r} ELSE @]
          /\ IF hasConflict
             THEN clientResponses' = [clientResponses EXCEPT ![cmd] = "slow"]
             ELSE IF ~hasConflict /\ Cardinality(quorumStatus'[cmd].responses) >= SuperQuorum
                  THEN clientResponses' = [clientResponses EXCEPT ![cmd] = "fast"]
                  ELSE UNCHANGED clientResponses
    /\ UNCHANGED <<speculativePool, uncommittedPool, commitIndex, leaderState, logEntries>>

ProcessProposeNonLeader(r, cmd) ==
    /\ leaderState.leader # r
    /\ clientResponses[cmd] = "pending"
    /\ LET specConflict == \E c \in speculativePool[r] : ConflictsWith(cmd, c)
       IN /\ quorumStatus' = [quorumStatus EXCEPT ![cmd].responses = @ \cup {r},
                                                  ![cmd].conflicts = IF specConflict THEN @ \cup {r} ELSE @]
    /\ UNCHANGED <<speculativePool, uncommittedPool, commitIndex, leaderState, clientResponses, logEntries>>

Commit ==
    /\ \E cmd \in Commands :
        /\ cmd \in uncommittedPool
        /\ commitIndex' = commitIndex + 1
        /\ logEntries' = Append(logEntries, cmd)
        /\ uncommittedPool' = uncommittedPool \ {cmd}
        /\ UNCHANGED <<speculativePool, leaderState, clientResponses, quorumStatus>>

ProcessCommitMsg(r, cmd) ==
    /\ commitIndex > 0
    /\ Len(logEntries) >= commitIndex
    /\ LET committedCmd == logEntries[commitIndex]
       IN /\ committedCmd = cmd
          /\ speculativePool' = [speculativePool EXCEPT ![r] = @ \ {cmd}]
          /\ IF clientResponses[cmd] = "slow"
             THEN clientResponses' = [clientResponses EXCEPT ![cmd] = "slow"]
             ELSE UNCHANGED clientResponses
    /\ UNCHANGED <<uncommittedPool, commitIndex, leaderState, logEntries, quorumStatus>>

LeaderChange(l) ==
    /\ l \in Replicas
    /\ leaderState.leader # l
    /\ LET recoveredPool == UNION {speculativePool[r] : r \in Replicas}
           quorumRecovered == {cmd \in recoveredPool : 
                               Cardinality({r \in Replicas : cmd \in speculativePool[r]}) >= RecoverQuorum}
       IN /\ leaderState' = [leader |-> l, term |-> leaderState.term + 1]
          /\ uncommittedPool' = quorumRecovered
          /\ speculativePool' = [r \in Replicas |-> 
                                 IF r = l THEN quorumRecovered ELSE speculativePool[r]]
    /\ UNCHANGED <<commitIndex, clientResponses, logEntries, quorumStatus>>

Next ==
    \/ \E cmd \in Commands : Propose(cmd)
    \/ \E r \in Replicas, cmd \in Commands : ProcessProposeLeader(r, cmd)
    \/ \E r \in Replicas, cmd \in Commands : ProcessProposeNonLeader(r, cmd)
    \/ Commit
    \/ \E r \in Replicas, cmd \in Commands : ProcessCommitMsg(r, cmd)
    \/ \E l \in Replicas : LeaderChange(l)

Spec == Init /\ [][Next]_vars

====