---- MODULE redisraft ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS
    NodeSet,        \* Set of all possible nodes
    ElectionTimeout \* Base election timeout value

VARIABLES
    state,          \* [node -> {FOLLOWER, CANDIDATE, LEADER, PRECANDIDATE}]
    currentTerm,    \* [node -> Nat]
    votedFor,       \* [node -> NodeSet ∪ {None}]
    log,            \* [node -> Seq([term: Nat, cmd: ANY])]
    commitIndex,    \* [node -> Nat]
    lastApplied,    \* [node -> Nat]
    nextIndex,      \* [node -> [node -> Nat]]
    matchIndex,     \* [node -> [node -> Nat]]
    votesReceived,  \* [node -> SUBSET NodeSet]
    leaderId,       \* [node -> NodeSet ∪ {None}]
    electionTimer,  \* [node -> Nat]
    electionTimeoutRand, \* [node -> Nat]
    snapshotIndex,  \* [node -> Nat]
    snapshotTerm,   \* [node -> Nat]
    config,         \* [node -> SUBSET NodeSet]
    messages        \* Bag of messages in transit

vars == <<state, currentTerm, votedFor, log, commitIndex, lastApplied, 
          nextIndex, matchIndex, votesReceived, leaderId, electionTimer,
          electionTimeoutRand, snapshotIndex, snapshotTerm, config, messages>>

NodeState == {"FOLLOWER", "CANDIDATE", "LEADER", "PRECANDIDATE"}
None == CHOOSE n : n \notin NodeSet

Init ==
    /\ state = [n \in NodeSet |-> "FOLLOWER"]
    /\ currentTerm = [n \in NodeSet |-> 0]
    /\ votedFor = [n \in NodeSet |-> None]
    /\ log = [n \in NodeSet |-> <<>>]
    /\ commitIndex = [n \in NodeSet |-> 0]
    /\ lastApplied = [n \in NodeSet |-> 0]
    /\ nextIndex = [n \in NodeSet |-> [m \in NodeSet |-> 1]]
    /\ matchIndex = [n \in NodeSet |-> [m \in NodeSet |-> 0]]
    /\ votesReceived = [n \in NodeSet |-> {}]
    /\ leaderId = [n \in NodeSet |-> None]
    /\ electionTimer = [n \in NodeSet |-> 0]
    /\ electionTimeoutRand = [n \in NodeSet |-> ElectionTimeout + (ElectionTimeout \div 2)]
    /\ snapshotIndex = [n \in NodeSet |-> 0]
    /\ snapshotTerm = [n \in NodeSet |-> 0]
    /\ config = [n \in NodeSet |-> NodeSet]
    /\ messages = EmptyBag

TypeInvariant ==
    /\ state \in [NodeSet -> NodeState]
    /\ currentTerm \in [NodeSet -> Nat]
    /\ votedFor \in [NodeSet -> NodeSet \cup {None}]
    /\ commitIndex \in [NodeSet -> Nat]
    /\ lastApplied \in [NodeSet -> Nat]
    /\ \A n \in NodeSet : lastApplied[n] <= commitIndex[n]
    /\ \A n \in NodeSet : Len(log[n]) >= commitIndex[n]
    /\ \A n \in NodeSet : electionTimer[n] \in Nat
    /\ \A n \in NodeSet : electionTimeoutRand[n] >= ElectionTimeout

Send(msg) == messages' = messages (+) {msg}

Receive(msg) == 
    /\ msg \in messages
    /\ messages' = messages (-) {msg}

BecomeFollower(n, term, leader) ==
    /\ state[n] \in {"CANDIDATE", "LEADER", "PRECANDIDATE"}
    /\ state' = [state EXCEPT ![n] = "FOLLOWER"]
    /\ currentTerm' = [currentTerm EXCEPT ![n] = term]
    /\ votedFor' = [votedFor EXCEPT ![n] = None]
    /\ leaderId' = [leaderId EXCEPT ![n] = leader]
    /\ electionTimer' = [electionTimer EXCEPT ![n] = 0]
    /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex, 
                  votesReceived, snapshotIndex, snapshotTerm, config, messages>>

BecomeCandidate(n) ==
    /\ state[n] = "FOLLOWER"
    /\ currentTerm' = [currentTerm EXCEPT ![n] = currentTerm[n] + 1]
    /\ votedFor' = [votedFor EXCEPT ![n] = n]
    /\ state' = [state EXCEPT ![n] = "CANDIDATE"]
    /\ votesReceived' = [votesReceived EXCEPT ![n] = {n}]
    /\ electionTimer' = [electionTimer EXCEPT ![n] = 0]
    /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex, 
                  leaderId, snapshotIndex, snapshotTerm, config, messages>>

BecomePreCandidate(n) ==
    /\ state[n] = "FOLLOWER"
    /\ state' = [state EXCEPT ![n] = "PRECANDIDATE"]
    /\ votesReceived' = [votesReceived EXCEPT ![n] = {}]
    /\ electionTimer' = [electionTimer EXCEPT ![n] = 0]
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, lastApplied, 
                  nextIndex, matchIndex, leaderId, snapshotIndex, snapshotTerm, 
                  config, messages>>

BecomeLeader(n) ==
    /\ state[n] = "CANDIDATE"
    /\ state' = [state EXCEPT ![n] = "LEADER"]
    /\ nextIndex' = [nextIndex EXCEPT ![n] = [m \in NodeSet |-> Len(log[n]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![n] = [m \in NodeSet |-> 0]]
    /\ electionTimer' = [electionTimer EXCEPT ![n] = 0]
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, lastApplied, 
                  votesReceived, leaderId, snapshotIndex, snapshotTerm, config, messages>>

RequestVote(n, m, term, candidateId, lastLogIndex, lastLogTerm, prevote) ==
    /\ Receive([type |-> "RequestVote", from |-> n, to |-> m, term |-> term,
                candidateId |-> candidateId, lastLogIndex |-> lastLogIndex,
                lastLogTerm |-> lastLogTerm, prevote |-> prevote])
    /\ \/ /\ prevote
          /\ term = currentTerm[n] + 1
       \/ /\ ~prevote
          /\ term >= currentTerm[n]
    /\ \/ term > currentTerm[n]
       \/ /\ term = currentTerm[n]
          /\ \/ votedFor[n] = None
             \/ votedFor[n] = candidateId
    /\ lastLogTerm >= LastTerm(log[n])
    /\ lastLogIndex >= Len(log[n])
    /\ votedFor' = IF ~prevote THEN [votedFor EXCEPT ![n] = candidateId] ELSE votedFor
    /\ currentTerm' = IF term > currentTerm[n] THEN [currentTerm EXCEPT ![n] = term] ELSE currentTerm
    /\ Send([type |-> "RequestVoteResponse", from |-> n, to |-> candidateId,
             term |-> currentTerm'[n], voteGranted |-> TRUE, prevote |-> prevote])
    /\ UNCHANGED <<state, log, commitIndex, lastApplied, nextIndex, matchIndex,
                  votesReceived, leaderId, electionTimer, electionTimeoutRand,
                  snapshotIndex, snapshotTerm, config>>

RequestVoteResponse(n, m, term, voteGranted, prevote) ==
    /\ Receive([type |-> "RequestVoteResponse", from |-> n, to |-> m,
                term |-> term, voteGranted |-> voteGranted, prevote |-> prevote])
    /\ \/ /\ prevote
          /\ state[m] = "PRECANDIDATE"
          /\ term = currentTerm[m] + 1
       \/ /\ ~prevote
          /\ state[m] = "CANDIDATE"
          /\ term = currentTerm[m]
    /\ \/ term > currentTerm[m]
          /\ BecomeFollower(m, term, None)
       \/ /\ term <= currentTerm[m]
          /\ voteGranted
          /\ votesReceived' = [votesReceived EXCEPT ![m] = votesReceived[m] \cup {n}]
          /\ \/ /\ Cardinality(votesReceived'[m]) > Cardinality(config[m]) \div 2
                /\ \/ /\ prevote
                      /\ BecomeCandidate(m)
                   \/ /\ ~prevote
                      /\ BecomeLeader(m)
             \/ UNCHANGED state
          /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, lastApplied,
                        nextIndex, matchIndex, leaderId, snapshotIndex, snapshotTerm,
                        config, electionTimer, electionTimeoutRand>>

AppendEntries(n, m, term, leaderId, prevLogIndex, prevLogTerm, entries, leaderCommit) ==
    /\ Receive([type |-> "AppendEntries", from |-> n, to |-> m, term |-> term,
                leaderId |-> leaderId, prevLogIndex |-> prevLogIndex,
                prevLogTerm |-> prevLogTerm, entries |-> entries,
                leaderCommit |-> leaderCommit])
    /\ \/ term > currentTerm[m]
          /\ BecomeFollower(m, term, leaderId)
       \/ term <= currentTerm[m]
          /\ \/ term < currentTerm[m]
                /\ Send([type |-> "AppendEntriesResponse", from |-> m, to |-> n,
                         term |-> currentTerm[m], success |-> FALSE,
                         matchIndex |-> Len(log[m])])
             \/ /\ term = currentTerm[m]
                /\ \/ prevLogIndex > Len(log[m])
                      \/ prevLogIndex > 0 /\ prevLogTerm /= LogTermAt(log[m], prevLogIndex)
                   /\ Send([type |-> "AppendEntriesResponse", from |-> m, to |-> n,
                            term |-> currentTerm[m], success |-> FALSE,
                            matchIndex |-> Len(log[m])])
                \/ /\ prevLogIndex <= Len(log[m])
                   /\ \/ prevLogIndex = 0
                      \/ prevLogTerm = LogTermAt(log[m], prevLogIndex)
                   /\ \* Truncate log if conflict
                   /\ LET newLog ==
                          IF prevLogIndex < Len(log[m]) THEN
                              SubSeq(log[m], 1, prevLogIndex) \o entries
                          ELSE log[m] \o entries
                      IN
                      /\ log' = [log EXCEPT ![m] = newLog]
                      /\ commitIndex' = [commitIndex EXCEPT ![m] = 
                              IF leaderCommit > commitIndex[m] THEN
                                  Min(leaderCommit, Len(newLog))
                              ELSE commitIndex[m]]
                      /\ Send([type |-> "AppendEntriesResponse", from |-> m, to |-> n,
                               term |-> currentTerm[m], success |-> TRUE,
                               matchIndex |-> Len(newLog)])
    /\ UNCHANGED <<state, currentTerm, votedFor, lastApplied, nextIndex, matchIndex,
                  votesReceived, electionTimer, electionTimeoutRand, snapshotIndex,
                  snapshotTerm, config>>

AppendEntriesResponse(n, m, term, success, matchIndex) ==
    /\ Receive([type |-> "AppendEntriesResponse", from |-> n, to |-> m,
                term |-> term, success |-> success, matchIndex |-> matchIndex])
    /\ state[m] = "LEADER"
    /\ \/ term > currentTerm[m]
          /\ BecomeFollower(m, term, None)
       \/ /\ term = currentTerm[m]
          /\ \/ ~success
                /\ nextIndex' = [nextIndex EXCEPT ![m][n] = nextIndex[m][n] - 1]
             \/ /\ success
                /\ nextIndex' = [nextIndex EXCEPT ![m][n] = matchIndex + 1]
                /\ matchIndex' = [matchIndex EXCEPT ![m][n] = matchIndex]
                /\ \* Update commit index
                /\ LET N == Max({k \in 1..Len(log[m]) : 
                                 Cardinality({n \in config[m] : matchIndex[m][n] >= k}) 
                                 > Cardinality(config[m]) \div 2})
                    IN
                    IF N > commitIndex[m] /\ LogTermAt(log[m], N) = currentTerm[m] THEN
                        commitIndex' = [commitIndex EXCEPT ![m] = N]
                    ELSE UNCHANGED commitIndex
    /\ UNCHANGED <<state, currentTerm, votedFor, log, lastApplied, votesReceived,
                  leaderId, electionTimer, electionTimeoutRand, snapshotIndex,
                  snapshotTerm, config>>

AdvanceTimer ==
    /\ \E n \in NodeSet :
        /\ electionTimer' = [electionTimer EXCEPT ![n] = electionTimer[n] + 1]
        /\ \/ /\ state[n] \in {"FOLLOWER", "CANDIDATE"}
              /\ electionTimer'[n] >= electionTimeoutRand[n]
              /\ \/ state[n] = "FOLLOWER"
                    /\ BecomePreCandidate(n)
                 \/ state[n] = "CANDIDATE"
                    /\ BecomeCandidate(n)
           \/ UNCHANGED state
        /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, lastApplied,
                      nextIndex, matchIndex, votesReceived, leaderId,
                      electionTimeoutRand, snapshotIndex, snapshotTerm, config, messages>>

Next ==
    \/ \E n, m \in NodeSet : RequestVote(n, m, currentTerm[n], n, Len(log[n]), LastTerm(log[n]), FALSE)
    \/ \E n, m \in NodeSet : RequestVoteResponse(n, m, currentTerm[n], TRUE, FALSE)
    \/ \E n, m \in NodeSet : AppendEntries(n, m, currentTerm[n], n, Len(log[n]), LastTerm(log[n]), <<>>, commitIndex[n])
    \/ \E n, m \in NodeSet : AppendEntriesResponse(n, m, currentTerm[n], TRUE, Len(log[m]))
    \/ AdvanceTimer

Termination ==
    /\ \A n \in NodeSet : state[n] = "LEADER" \/ state[n] = "FOLLOWER"
    /\ \E leader \in NodeSet :
        /\ state[leader] = "LEADER"
        /\ \A n \in NodeSet : 
            /\ state[n] = "FOLLOWER" 
            /\ leaderId[n] = leader
            /\ currentTerm[n] = currentTerm[leader]

=============================================================================
\* End of module
====