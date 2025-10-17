---- MODULE redisraft ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS
    Node,           \* The set of servers, e.g., {"n1", "n2", "n3"}
    Command,        \* The set of client commands
    Nil             \* A value indicating no vote

VARIABLES
    state,          \* The state of each server (Follower, PreCandidate, Candidate, Leader)
    currentTerm,    \* The current term of each server
    votedFor,       \* The candidate each server voted for in the current term
    log,            \* The log of each server
    commitIndex,    \* The index of the highest log entry known to be committed
    lastApplied,    \* The index of the highest log entry applied to the state machine
    
    nextIndex,      \* For each leader, the next log index to send to each follower
    matchIndex,     \* For each leader, the highest log index known to be replicated on each follower
    
    votesGranted,   \* For each candidate, the set of servers that voted for it
    preVotesGranted,\* For each pre-candidate, the set of servers that granted a pre-vote
    
    messages,       \* The set of messages in the network
    
    clusterConfig   \* Each node's view of the current cluster configuration

vars == <<state, currentTerm, votedFor, log, commitIndex, lastApplied,
          nextIndex, matchIndex, votesGranted, preVotesGranted, messages, clusterConfig>>

TypeOK ==
    /\ state \in [Node -> {"Follower", "PreCandidate", "Candidate", "Leader"}]
    /\ currentTerm \in [Node -> Nat]
    /\ votedFor \in [Node -> Node \cup {Nil}]
    /\ \A n \in Node: IsSequence(log[n])
    /\ commitIndex \in [Node -> Nat]
    /\ lastApplied \in [Node -> Nat]
    /\ nextIndex \in [Node -> [Node -> Nat \ {0}]]
    /\ matchIndex \in [Node -> [Node -> Nat]]
    /\ votesGranted \in [Node -> SUBSET Node]
    /\ preVotesGranted \in [Node -> SUBSET Node]
    /\ \A msg \in messages:
        \/ msg.type \in {"RequestVote", "AppendEntries", "InstallSnapshot"}
        \/ msg.type \in {"RequestVoteResponse", "AppendEntriesResponse", "InstallSnapshotResponse"}
    /\ clusterConfig \in [Node -> SUBSET Node]

\* Helper operators
LastLogIndex(n) == Len(log[n])
LastLogTerm(n) == IF LastLogIndex(n) > 0 THEN log[n][LastLogIndex(n)].term ELSE 0

IsMoreUpToDate(term1, index1, term2, index2) ==
    \/ term1 > term2
    \/ (term1 = term2 /\ index1 >= index2)

IsQuorum(n, s) == Cardinality(s) * 2 > Cardinality(clusterConfig[n])

BecomeFollower(n, term) ==
    /\ state' = [state EXCEPT ![n] = "Follower"]
    /\ currentTerm' = [currentTerm EXCEPT ![n] = term]
    /\ votedFor' = [votedFor EXCEPT ![n] = Nil]
    /\ preVotesGranted' = [preVotesGranted EXCEPT ![n] = {}]
    /\ votesGranted' = [votesGranted EXCEPT ![n] = {}]

\* Initial state
Init ==
    /\ state = [n \in Node |-> "Follower"]
    /\ currentTerm = [n \in Node |-> 0]
    /\ votedFor = [n \in Node |-> Nil]
    /\ log = [n \in Node |-> << >>]
    /\ commitIndex = [n \in Node |-> 0]
    /\ lastApplied = [n \in Node |-> 0]
    /\ nextIndex = [n \in Node |-> [f \in Node |-> 1]]
    /\ matchIndex = [n \in Node |-> [f \in Node |-> 0]]
    /\ votesGranted = [n \in Node |-> {}]
    /\ preVotesGranted = [n \in Node |-> {}]
    /\ messages = {}
    /\ clusterConfig = [n \in Node |-> Node]

\* Actions

\* A follower, pre-candidate, or candidate times out and starts an election.
ElectionTimeout(n) ==
    /\ state[n] \in {"Follower", "PreCandidate", "Candidate"}
    /\ \/ /\ state[n] = "Follower" \* Becomes PreCandidate
           /\ state' = [state EXCEPT ![n] = "PreCandidate"]
           /\ preVotesGranted' = [preVotesGranted EXCEPT ![n] = {n}]
           /\ messages' = messages \cup
                {[ type |-> "RequestVote",
                   term |-> currentTerm[n] + 1,
                   candidateId |-> n,
                   lastLogIndex |-> LastLogIndex(n),
                   lastLogTerm |-> LastLogTerm(n),
                   prevote |-> TRUE,
                   dest |-> p ]
                 | p \in clusterConfig[n] \ {n}}
           /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, votesGranted, clusterConfig>>

       \/ /\ state[n] \in {"PreCandidate", "Candidate"} \* Restarts election
          /\ \/ /\ state[n] = "PreCandidate" \* Restarts pre-vote
                 /\ state' = [state EXCEPT ![n] = "PreCandidate"]
                 /\ preVotesGranted' = [preVotesGranted EXCEPT ![n] = {n}]
                 /\ messages' = messages \cup
                      {[ type |-> "RequestVote",
                         term |-> currentTerm[n] + 1,
                         candidateId |-> n,
                         lastLogIndex |-> LastLogIndex(n),
                         lastLogTerm |-> LastLogTerm(n),
                         prevote |-> TRUE,
                         dest |-> p ]
                       | p \in clusterConfig[n] \ {n}}
                 /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, votesGranted, clusterConfig>>
             \/ /\ state[n] = "Candidate" \* Restarts real vote
                 /\ currentTerm' = [currentTerm EXCEPT ![n] = currentTerm[n] + 1]
                 /\ votedFor' = [votedFor EXCEPT ![n] = n]
                 /\ votesGranted' = [votesGranted EXCEPT ![n] = {n}]
                 /\ messages' = messages \cup
                      {[ type |-> "RequestVote",
                         term |-> currentTerm[n] + 1,
                         candidateId |-> n,
                         lastLogIndex |-> LastLogIndex(n),
                         lastLogTerm |-> LastLogTerm(n),
                         prevote |-> FALSE,
                         dest |-> p ]
                       | p \in clusterConfig[n] \ {n}}
                 /\ UNCHANGED <<state, log, commitIndex, lastApplied, nextIndex, matchIndex, preVotesGranted, clusterConfig>>

\* A server receives a RequestVote message.
HandleRequestVote(n) ==
    \E m \in messages:
        /\ m.type = "RequestVote"
        /\ m.dest = n
        /\ LET voteGranted ==
                /\ m.term >= currentTerm[n]
                /\ (IF m.term > currentTerm[n] THEN TRUE ELSE votedFor[n] \in {Nil, m.candidateId})
                /\ IsMoreUpToDate(m.lastLogTerm, m.lastLogIndex, LastLogTerm(n), LastLogIndex(n))
           newTerm == IF m.term > currentTerm[n] THEN m.term ELSE currentTerm[n]
        IN
        /\ IF m.term > currentTerm[n] /\ \lnot m.prevote
           THEN /\ state' = [state EXCEPT ![n] = "Follower"]
                /\ currentTerm' = [currentTerm EXCEPT ![n] = m.term]
                /\ preVotesGranted' = [preVotesGranted EXCEPT ![n] = {}]
                /\ votesGranted' = [votesGranted EXCEPT ![n] = {}]
                /\ IF voteGranted
                   THEN votedFor' = [votedFor EXCEPT ![n] = m.candidateId]
                   ELSE votedFor' = [votedFor EXCEPT ![n] = Nil]
           ELSE /\ UNCHANGED <<state, currentTerm, votedFor, preVotesGranted, votesGranted>>
        /\ messages' = (messages \ {m}) \cup
             {[ type |-> "RequestVoteResponse",
                term |-> newTerm,
                requestTerm |-> m.term,
                voteGranted |-> voteGranted,
                prevote |-> m.prevote,
                src |-> n,
                dest |-> m.candidateId ]}
        /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex, clusterConfig>>

\* A candidate or pre-candidate receives a RequestVoteResponse.
HandleRequestVoteResponse(n) ==
    \E m \in messages:
        /\ m.type = "RequestVoteResponse"
        /\ m.dest = n
        /\ IF m.term > currentTerm[n]
           THEN /\ BecomeFollower(n, m.term)
                /\ messages' = messages \ {m}
                /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex, clusterConfig>>
           ELSE /\ \/ /\ m.prevote /\ state[n] = "PreCandidate" /\ m.requestTerm = currentTerm[n] + 1
                       /\ IF m.voteGranted
                          THEN LET newPreVotes == preVotesGranted[n] \cup {m.src}
                               IN /\ preVotesGranted' = [preVotesGranted EXCEPT ![n] = newPreVotes]
                                  /\ IF IsQuorum(n, newPreVotes) /\ state[n] # "Candidate"
                                     THEN \* Become Candidate
                                         /\ state' = [state EXCEPT ![n] = "Candidate"]
                                         /\ currentTerm' = [currentTerm EXCEPT ![n] = currentTerm[n] + 1]
                                         /\ votedFor' = [votedFor EXCEPT ![n] = n]
                                         /\ votesGranted' = [votesGranted EXCEPT ![n] = {n}]
                                         /\ messages' = (messages \ {m}) \cup
                                              {[ type |-> "RequestVote",
                                                 term |-> currentTerm[n] + 1,
                                                 candidateId |-> n,
                                                 lastLogIndex |-> LastLogIndex(n),
                                                 lastLogTerm |-> LastLogTerm(n),
                                                 prevote |-> FALSE,
                                                 dest |-> p ]
                                               | p \in clusterConfig[n] \ {n}}
                                     ELSE /\ UNCHANGED <<state, currentTerm, votedFor, votesGranted>>
                                          /\ messages' = messages \ {m}
                          ELSE /\ UNCHANGED <<preVotesGranted, state, currentTerm, votedFor, votesGranted>>
                               /\ messages' = messages \ {m}
                  \/ /\ \lnot m.prevote /\ state[n] = "Candidate" /\ m.requestTerm = currentTerm[n]
                       /\ IF m.voteGranted
                          THEN LET newVotes == votesGranted[n] \cup {m.src}
                               IN /\ votesGranted' = [votesGranted EXCEPT ![n] = newVotes]
                                  /\ IF IsQuorum(n, newVotes) /\ state[n] # "Leader"
                                     THEN \* Become Leader
                                         /\ state' = [state EXCEPT ![n] = "Leader"]
                                         /\ nextIndex' = [nextIndex EXCEPT ![n] = [p \in Node |-> LastLogIndex(n) + 1]]
                                         /\ matchIndex' = [matchIndex EXCEPT ![n] = [p \in Node |-> 0]]
                                         /\ log' = [log EXCEPT ![n] = Append(log[n], [term |-> currentTerm[n], command |-> "NO-OP"])]
                                         /\ messages' = messages \ {m}
                                     ELSE /\ UNCHANGED <<state, nextIndex, matchIndex, log>>
                                          /\ messages' = messages \ {m}
                          ELSE /\ UNCHANGED <<votesGranted, state, nextIndex, matchIndex, log>>
                               /\ messages' = messages \ {m}
                  \/ /\ TRUE \* Stale response, ignore
                       /\ UNCHANGED <<state, currentTerm, votedFor, log, nextIndex, matchIndex, votesGranted, preVotesGranted>>
                       /\ messages' = messages \ {m}
                /\ UNCHANGED <<commitIndex, lastApplied, clusterConfig>>

\* A leader sends AppendEntries (can be a heartbeat if entries is empty).
LeaderSendAppendEntries(l, f) ==
    /\ state[l] = "Leader"
    /\ f \in clusterConfig[l] \ {l}
    /\ LET prevLogIndex == nextIndex[l][f] - 1
           prevLogTerm == IF prevLogIndex > 0 THEN log[l][prevLogIndex].term ELSE 0
           entries == SubSeq(log[l], nextIndex[l][f], LastLogIndex(l))
    IN
    /\ messages' = messages \cup
        {[ type |-> "AppendEntries",
           term |-> currentTerm[l],
           leaderId |-> l,
           prevLogIndex |-> prevLogIndex,
           prevLogTerm |-> prevLogTerm,
           entries |-> entries,
           leaderCommit |-> commitIndex[l],
           dest |-> f ]}
    /\ UNCHANGED vars

\* A server receives an AppendEntries message.
HandleAppendEntries(n) ==
    \E m \in messages:
        /\ m.type = "AppendEntries"
        /\ m.dest = n
        /\ IF m.term < currentTerm[n]
           THEN /\ messages' = (messages \ {m}) \cup
                    {[ type |-> "AppendEntriesResponse",
                       term |-> currentTerm[n],
                       success |-> FALSE,
                       matchIndex |-> 0,
                       src |-> n,
                       dest |-> m.leaderId ]}
                /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, votesGranted, preVotesGranted, clusterConfig>>
           ELSE /\ LET followerVars == BecomeFollower(n, m.term)
                IN
                /\ followerVars
                /\ LET logOK == m.prevLogIndex = 0
                                \/ (m.prevLogIndex > 0 /\ m.prevLogIndex <= LastLogIndex(n)
                                    /\ log[n][m.prevLogIndex].term = m.prevLogTerm)
                IN
                /\ IF \lnot logOK
                   THEN /\ messages' = (messages \ {m}) \cup
                            {[ type |-> "AppendEntriesResponse",
                               term |-> currentTerm'[n],
                               success |-> FALSE,
                               matchIndex |-> 0,
                               src |-> n,
                               dest |-> m.leaderId ]}
                        /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex, clusterConfig>>
                   ELSE /\ LET
                              conflictIndexSet ==
                                { i \in DOMAIN m.entries:
                                    /\ m.prevLogIndex + i <= LastLogIndex(n)
                                    /\ log[n][m.prevLogIndex + i].term # m.entries[i].term },
                              newLog ==
                                IF conflictIndexSet = {}
                                THEN Append(log[n], SubSeq(m.entries, LastLogIndex(log[n]) - m.prevLogIndex + 1, Len(m.entries)))
                                ELSE LET conflictIndex == Min(conflictIndexSet)
                                     IN Append(SubSeq(log[n], 1, m.prevLogIndex + conflictIndex - 1), m.entries)
                          IN
                          /\ log' = [log EXCEPT ![n] = newLog]
                          /\ IF m.leaderCommit > commitIndex[n]
                             THEN commitIndex' = [commitIndex EXCEPT ![n] = min({m.leaderCommit, LastLogIndex(newLog)})]
                             ELSE UNCHANGED commitIndex
                          /\ messages' = (messages \ {m}) \cup
                               {[ type |-> "AppendEntriesResponse",
                                  term |-> currentTerm'[n],
                                  success |-> TRUE,
                                  matchIndex |-> m.prevLogIndex + Len(m.entries),
                                  src |-> n,
                                  dest |-> m.leaderId ]}
                          /\ UNCHANGED <<lastApplied, nextIndex, matchIndex, clusterConfig>>

\* A leader receives an AppendEntriesResponse.
HandleAppendEntriesResponse(l) ==
    \E m \in messages:
        /\ m.type = "AppendEntriesResponse"
        /\ m.dest = l
        /\ state[l] = "Leader"
        /\ messages' = messages \ {m}
        /\ IF m.term > currentTerm[l]
           THEN /\ BecomeFollower(l, m.term)
                /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex, clusterConfig>>
           ELSE /\ IF m.success
                   THEN /\ nextIndex' = [nextIndex EXCEPT ![l][m.src] = m.matchIndex + 1]
                        /\ matchIndex' = [matchIndex EXCEPT ![l][m.src] = m.matchIndex]
                   ELSE /\ nextIndex' = [nextIndex EXCEPT ![l][m.src] = max({1, nextIndex[l][m.src] - 1})]
                        /\ UNCHANGED matchIndex
                /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, votesGranted, preVotesGranted, clusterConfig>>

\* A leader advances its commit index.
LeaderAdvanceCommitIndex(l) ==
    /\ state[l] = "Leader"
    /\ LET possible_N ==
            { N \in commitIndex[l]+1 .. LastLogIndex(l):
                /\ log[l][N].term = currentTerm[l]
                /\ IsQuorum(l, {p \in clusterConfig[l] | matchIndex[l][p] >= N} \cup {l}) }
    IN
    /\ possible_N # {}
    /\ LET newCommitIndex == Max(possible_N)
       IN commitIndex' = [commitIndex EXCEPT ![l] = newCommitIndex]
    /\ UNCHANGED <<state, currentTerm, votedFor, log, lastApplied, nextIndex, matchIndex, votesGranted, preVotesGranted, messages, clusterConfig>>

\* A server applies a committed entry to its state machine.
ApplyToStateMachine(n) ==
    /\ commitIndex[n] > lastApplied[n]
    /\ LET newLastApplied == lastApplied[n] + 1
           entry == log[n][newLastApplied]
    IN
    /\ lastApplied' = [lastApplied EXCEPT ![n] = newLastApplied]
    /\ IF entry.command.type = "config_change"
       THEN clusterConfig' = [clusterConfig EXCEPT ![n] = entry.command.config]
       ELSE UNCHANGED clusterConfig
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, votesGranted, preVotesGranted, messages>>

\* A client sends a request to the leader.
ClientRequest(l, cmd) ==
    /\ state[l] = "Leader"
    /\ cmd \in Command
    /\ log' = [log EXCEPT ![l] = Append(log[l], [term |-> currentTerm[l], command |-> cmd])]
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, lastApplied, nextIndex, matchIndex, votesGranted, preVotesGranted, messages, clusterConfig>>

\* A leader decides to create a snapshot.
LeaderDecidesToSnapshot(l) ==
    /\ state[l] = "Leader"
    /\ commitIndex[l] > 0
    /\ LET lastIncludedIndex == commitIndex[l]
           lastIncludedTerm == log[l][lastIncludedIndex].term
           newLog == SubSeq(log[l], lastIncludedIndex + 1, Len(log[l]))
    IN
    /\ log' = [log EXCEPT ![l] = newLog]
    /\ messages' = messages \cup
        {[ type |-> "InstallSnapshot",
           term |-> currentTerm[l],
           leaderId |-> l,
           lastIncludedIndex |-> lastIncludedIndex,
           lastIncludedTerm |-> lastIncludedTerm,
           dest |-> f ]
         | f \in clusterConfig[l] \ {l}}
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, lastApplied, nextIndex, matchIndex, votesGranted, preVotesGranted, clusterConfig>>

\* A follower receives and installs a snapshot.
FollowerInstallsSnapshot(n) ==
    \E m \in messages:
        /\ m.type = "InstallSnapshot"
        /\ m.dest = n
        /\ messages' = messages \ {m}
        /\ IF m.term < currentTerm[n]
           THEN UNCHANGED vars
           ELSE /\ BecomeFollower(n, m.term)
                /\ log' = [log EXCEPT ![n] = << >>] \* Abstractly, log is replaced by snapshot
                /\ commitIndex' = [commitIndex EXCEPT ![n] = m.lastIncludedIndex]
                /\ lastApplied' = [lastApplied EXCEPT ![n] = m.lastIncludedIndex]
                /\ UNCHANGED <<nextIndex, matchIndex, clusterConfig>>

\* A leader receives a request to add a node.
AddNodeRequest(l, newNode) ==
    /\ state[l] = "Leader"
    /\ newNode \notin clusterConfig[l]
    /\ LET newConfig == clusterConfig[l] \cup {newNode}
           cmd == [type |-> "config_change", config |-> newConfig]
    IN
    /\ log' = [log EXCEPT ![l] = Append(log[l], [term |-> currentTerm[l], command |-> cmd])]
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, lastApplied, nextIndex, matchIndex, votesGranted, preVotesGranted, messages, clusterConfig>>

\* A leader receives a request to remove a node.
RemoveNodeRequest(l, oldNode) ==
    /\ state[l] = "Leader"
    /\ oldNode \in clusterConfig[l] \ {l}
    /\ LET newConfig == clusterConfig[l] \ {oldNode}
           cmd == [type |-> "config_change", config |-> newConfig]
    IN
    /\ log' = [log EXCEPT ![l] = Append(log[l], [term |-> currentTerm[l], command |-> cmd])]
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, lastApplied, nextIndex, matchIndex, votesGranted, preVotesGranted, messages, clusterConfig>>

Next ==
    \/ \E n \in Node: ElectionTimeout(n)
    \/ \E n \in Node: HandleRequestVote(n)
    \/ \E n \in Node: HandleRequestVoteResponse(n)
    \/ \E l \in Node, f \in Node: LeaderSendAppendEntries(l, f)
    \/ \E n \in Node: HandleAppendEntries(n)
    \/ \E l \in Node: HandleAppendEntriesResponse(l)
    \/ \E l \in Node: LeaderAdvanceCommitIndex(l)
    \/ \E n \in Node: ApplyToStateMachine(n)
    \/ \E l \in Node, cmd \in Command: ClientRequest(l, cmd)
    \/ \E l \in Node: LeaderDecidesToSnapshot(l)
    \/ \E n \in Node: FollowerInstallsSnapshot(n)
    \/ \E l \in Node, n \in Node: AddNodeRequest(l, n)
    \/ \E l \in Node, n \in Node: RemoveNodeRequest(l, n)

Spec == Init /\ [][Next]_vars

====
