---- MODULE curp ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS
    Replicas,
    Commands,
    MaxTerm,
    MaxLogIndex

VARIABLES
    \* Core state variables
    role,
    term,
    votedFor,
    leaderID,
    log,
    commitIndex,
    lastApplied,
    
    \* CURP-specific state
    speculativePool,
    uncommittedPool,
    
    \* Leader state
    nextIndex,
    matchIndex,
    transferee,
    
    \* Client interaction
    clientRequests,
    responses,
    
    \* Network abstraction
    messages

vars == <<role, term, votedFor, leaderID, log, commitIndex, lastApplied,
          speculativePool, uncommittedPool, nextIndex, matchIndex, transferee,
          clientRequests, responses, messages>>

\* Type definitions
Roles == {"Follower", "Candidate", "Leader"}
LogEntry == [term: Nat, index: Nat, cmd: Commands, proposeId: Nat]
Message == [type: STRING, from: Replicas, to: Replicas, term: Nat]

\* Helper functions
IsLeader(r) == role[r] = "Leader"
IsQuorum(S) == Cardinality(S) * 2 > Cardinality(Replicas)
IsSuperQuorum(S) == Cardinality(S) * 2 > Cardinality(Replicas) + (Cardinality(Replicas) - Cardinality(S \intersect Replicas))
IsRecoverQuorum(S) == Cardinality(S) * 4 > Cardinality(Replicas) + 2

\* Key extraction for conflict detection
KeysOf(cmd) == {cmd}  \* Simplified: each command has its own key

\* Conflict detection
ConflictsWith(cmd1, cmd2) == KeysOf(cmd1) \intersect KeysOf(cmd2) # {}

\* Initial state
Init ==
    /\ role = [r \in Replicas |-> "Follower"]
    /\ term = [r \in Replicas |-> 0]
    /\ votedFor = [r \in Replicas |-> "None"]
    /\ leaderID = [r \in Replicas |-> "None"]
    /\ log = [r \in Replicas |-> <<>>]
    /\ commitIndex = [r \in Replicas |-> 0]
    /\ lastApplied = [r \in Replicas |-> 0]
    /\ speculativePool = [r \in Replicas |-> {}]
    /\ uncommittedPool = [r \in Replicas |-> {}]
    /\ nextIndex = [r \in Replicas |-> [s \in Replicas |-> 1]]
    /\ matchIndex = [r \in Replicas |-> [s \in Replicas |-> 0]]
    /\ transferee = [r \in Replicas |-> "None"]
    /\ clientRequests = {}
    /\ responses = {}
    /\ messages = {}

\* Client Proposal
Propose(cmd) ==
    /\ cmd \in Commands
    /\ clientRequests' = clientRequests \union {cmd}
    /\ UNCHANGED <<role, term, votedFor, leaderID, log, commitIndex, lastApplied,
                   speculativePool, uncommittedPool, nextIndex, matchIndex, transferee,
                   responses, messages>>

\* Leader Processing - detects conflicts in both speculative and uncommitted pools
ProcessProposeLeader(r, cmd) ==
    /\ IsLeader(r)
    /\ cmd \in clientRequests
    /\ LET conflictSpec == \E c \in speculativePool[r] : ConflictsWith(cmd, c)
           conflictUnc == \E c \in uncommittedPool[r] : ConflictsWith(cmd, c)
           conflict == conflictSpec \/ conflictUnc
           newEntry == [term |-> term[r], index |-> Len(log[r]) + 1, cmd |-> cmd, proposeId |-> Len(log[r]) + 1]
       IN
       /\ log' = [log EXCEPT ![r] = Append(@, newEntry)]
       /\ speculativePool' = [speculativePool EXCEPT ![r] = @ \union {cmd}]
       /\ uncommittedPool' = [uncommittedPool EXCEPT ![r] = @ \union {cmd}]
       /\ IF ~conflict
          THEN responses' = responses \union {[cmd |-> cmd, result |-> "fast_path", replica |-> r]}
          ELSE responses' = responses \union {[cmd |-> cmd, result |-> "slow_path", replica |-> r]}
       /\ clientRequests' = clientRequests \ {cmd}
       /\ UNCHANGED <<role, term, votedFor, leaderID, commitIndex, lastApplied,
                      nextIndex, matchIndex, transferee, messages>>

\* Non-leader Processing - detects conflicts only in speculative pool
ProcessProposeNonLeader(r, cmd) ==
    /\ ~IsLeader(r)
    /\ cmd \in clientRequests
    /\ LET conflictSpec == \E c \in speculativePool[r] : ConflictsWith(cmd, c)
       IN
       /\ speculativePool' = [speculativePool EXCEPT ![r] = @ \union {cmd}]
       /\ responses' = responses \union {[cmd |-> cmd, conflict |-> conflictSpec, replica |-> r]}
       /\ clientRequests' = clientRequests \ {cmd}
       /\ UNCHANGED <<role, term, votedFor, leaderID, log, commitIndex, lastApplied,
                      uncommittedPool, nextIndex, matchIndex, transferee, messages>>

\* Backend Protocol Commit - abstract consensus protocol commits an uncommitted command
Commit ==
    /\ \E r \in Replicas, i \in DOMAIN log[r] :
        /\ IsLeader(r)
        /\ i > commitIndex[r]
        /\ LET entry == log[r][i]
               replicatedCount == Cardinality({s \in Replicas : 
                   /\ Len(log[s]) >= i 
                   /\ log[s][i] = entry})
           IN
           /\ IsQuorum({s \in Replicas : Len(log[s]) >= i /\ log[s][i] = entry})
           /\ commitIndex' = [commitIndex EXCEPT ![r] = i]
           /\ messages' = messages \union {[type |-> "commit", from |-> r, to |-> s, 
                                           term |-> term[r], index |-> i] : s \in Replicas \ {r}}
           /\ UNCHANGED <<role, term, votedFor, leaderID, log, lastApplied,
                          speculativePool, uncommittedPool, nextIndex, matchIndex, transferee,
                          clientRequests, responses>>

\* Commit Processing - processes committed command and applies garbage collection
ProcessCommitMsg(r, cmd) ==
    /\ \E msg \in messages :
        /\ msg.type = "commit"
        /\ msg.to = r
        /\ LET commitIdx == msg.index
           IN
           /\ commitIdx <= Len(log[r])
           /\ commitIndex' = [commitIndex EXCEPT ![r] = commitIdx]
           /\ lastApplied' = [lastApplied EXCEPT ![r] = commitIdx]
           /\ LET committedCmd == log[r][commitIdx].cmd
              IN
              /\ speculativePool' = [speculativePool EXCEPT ![r] = @ \ {committedCmd}]
              /\ uncommittedPool' = [uncommittedPool EXCEPT ![r] = @ \ {committedCmd}]
           /\ messages' = messages \ {msg}
           /\ UNCHANGED <<role, term, votedFor, leaderID, log, nextIndex, matchIndex, transferee,
                          clientRequests, responses>>

\* Backend Protocol Leader Change - abstract consensus elects new leader with recovery
LeaderChange(l) ==
    /\ l \in Replicas
    /\ \E oldLeader \in Replicas : IsLeader(oldLeader) /\ oldLeader # l
    /\ LET quorumReplicas == CHOOSE S \in SUBSET Replicas : 
                                /\ l \in S 
                                /\ IsQuorum(S)
           recoveredSpecs == UNION {speculativePool[r] : r \in quorumReplicas}
           recoverableSpecs == {cmd \in recoveredSpecs : 
                                 Cardinality({r \in quorumReplicas : cmd \in speculativePool[r]}) >= 
                                 Cardinality(quorumReplicas) \div 2 + 1}
       IN
       /\ role' = [r \in Replicas |-> IF r = l THEN "Leader" ELSE "Follower"]
       /\ term' = [r \in Replicas |-> IF r = l THEN term[r] + 1 ELSE term[r]]
       /\ leaderID' = [r \in Replicas |-> l]
       /\ speculativePool' = [speculativePool EXCEPT ![l] = recoverableSpecs]
       /\ uncommittedPool' = [uncommittedPool EXCEPT ![l] = recoverableSpecs]
       /\ nextIndex' = [nextIndex EXCEPT ![l] = [s \in Replicas |-> Len(log[l]) + 1]]
       /\ matchIndex' = [matchIndex EXCEPT ![l] = [s \in Replicas |-> 0]]
       /\ transferee' = [transferee EXCEPT ![l] = "None"]
       /\ UNCHANGED <<votedFor, log, commitIndex, lastApplied, clientRequests, responses, messages>>

\* Next state relation
Next ==
    \/ \E cmd \in Commands : Propose(cmd)
    \/ \E r \in Replicas, cmd \in Commands : ProcessProposeLeader(r, cmd)
    \/ \E r \in Replicas, cmd \in Commands : ProcessProposeNonLeader(r, cmd)
    \/ Commit
    \/ \E r \in Replicas, cmd \in Commands : ProcessCommitMsg(r, cmd)
    \/ \E l \in Replicas : LeaderChange(l)

\* Specification
Spec == Init /\ [][Next]_vars

====