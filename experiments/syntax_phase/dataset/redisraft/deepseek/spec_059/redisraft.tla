---- MODULE redisraft ----
EXTENDS TLC, Sequences, Naturals, FiniteSets, Bags

CONSTANTS Node, NoNode

VARIABLES
    state,
    currentTerm,
    votedFor,
    log,
    commitIndex,
    lastApplied,
    nextIndex,
    matchIndex,
    leaderId,
    electionTimeout,
    electionTimer,
    votes,
    messages,
    snapshotIndex,
    snapshotTerm,
    cfgChangeIndex

vars == <<state, currentTerm, votedFor, log, commitIndex, lastApplied, 
          nextIndex, matchIndex, leaderId, electionTimeout, electionTimer,
          votes, messages, snapshotIndex, snapshotTerm, cfgChangeIndex>>

\* Type invariants
TypeInvariant ==
    /\ state \in [Node -> {"Follower", "Candidate", "Leader", "PreCandidate"}]
    /\ currentTerm \in [Node -> Nat]
    /\ votedFor \in [Node -> Node \cup {NoNode}]
    /\ log \in [Node -> Seq([term: Nat, type: {"Normal", "Config"}, data: {}])]
    /\ commitIndex \in [Node -> Nat]
    /\ lastApplied \in [Node -> Nat]
    /\ nextIndex \in [Node -> [Node -> Nat]]
    /\ matchIndex \in [Node -> [Node -> Nat]]
    /\ leaderId \in [Node -> Node \cup {NoNode}]
    /\ electionTimeout \in [Node -> Nat]
    /\ electionTimer \in [Node -> Nat]
    /\ votes \in [Node -> SUBSET Node]
    /\ messages \in Bag([type: {"RequestVote", "RequestVoteResponse", "AppendEntries", "AppendEntriesResponse"}, 
                         from: Node, to: Node, term: Nat,
                         candidateId: Node \cup {NoNode}, lastLogIndex: Nat, lastLogTerm: Nat, prevote: BOOLEAN,
                         voteGranted: BOOLEAN, requestTerm: Nat,
                         prevLogIndex: Nat, prevLogTerm: Nat, entries: Seq([]), leaderCommit: Nat,
                         success: BOOLEAN, currentIndex: Nat, msgId: Nat])
    /\ snapshotIndex \in [Node -> Nat]
    /\ snapshotTerm \in [Node -> Nat]
    /\ cfgChangeIndex \in [Node -> Int \cup {-1}]

\* Helper functions
IsFollower(n) == state[n] = "Follower"
IsCandidate(n) == state[n] = "Candidate"
IsLeader(n) == state[n] = "Leader"
IsPreCandidate(n) == state[n] = "PreCandidate"

LogTerm(log, idx) ==
    IF idx = 0 THEN 0
    ELSE IF idx <= Len(log) THEN log[idx].term
    ELSE 0

LastLogIndex(n) == Len(log[n])
LastLogTerm(n) == 
    IF LastLogIndex(n) > 0 THEN log[n][LastLogIndex(n)].term
    ELSE 0

Majority == Cardinality(Node) \div 2 + 1

HasMajorityVotes(n) == Cardinality(votes[n]) >= Majority

LogUpToDate(n, lastLogIndex, lastLogTerm) ==
    \/ lastLogTerm > LastLogTerm(n)
    \/ lastLogTerm = LastLogTerm(n) /\ lastLogIndex >= LastLogIndex(n)

\* Message constructors
MakeRequestVote(from, to, term, candidateId, lastLogIndex, lastLogTerm, prevote) ==
    [type |-> "RequestVote", from |-> from, to |-> to, term |-> term,
     candidateId |-> candidateId, lastLogIndex |-> lastLogIndex, 
     lastLogTerm |-> lastLogTerm, prevote |-> prevote]

MakeRequestVoteResponse(from, to, term, voteGranted, requestTerm, prevote) ==
    [type |-> "RequestVoteResponse", from |-> from, to |-> to, term |-> term,
     voteGranted |-> voteGranted, requestTerm |-> requestTerm, prevote |-> prevote]

MakeAppendEntries(from, to, term, prevLogIndex, prevLogTerm, entries, leaderCommit, msgId) ==
    [type |-> "AppendEntries", from |-> from, to |-> to, term |-> term,
     prevLogIndex |-> prevLogIndex, prevLogTerm |-> prevLogTerm,
     entries |-> entries, leaderCommit |-> leaderCommit, msgId |-> msgId]

MakeAppendEntriesResponse(from, to, term, success, currentIndex, msgId) ==
    [type |-> "AppendEntriesResponse", from |-> from, to |-> to, term |-> term,
     success |-> success, currentIndex |-> currentIndex, msgId |-> msgId]

\* Initial state
Init ==
    /\ state = [n \in Node |-> "Follower"]
    /\ currentTerm = [n \in Node |-> 0]
    /\ votedFor = [n \in Node |-> NoNode]
    /\ log = [n \in Node |-> <<>>]
    /\ commitIndex = [n \in Node |-> 0]
    /\ lastApplied = [n \in Node |-> 0]
    /\ nextIndex = [n \in Node |-> [m \in Node |-> 1]]
    /\ matchIndex = [n \in Node |-> [m \in Node |-> 0]]
    /\ leaderId = [n \in Node |-> NoNode]
    /\ electionTimeout = [n \in Node |-> 3]
    /\ electionTimer = [n \in Node |-> 0]
    /\ votes = [n \in Node |-> {}]
    /\ messages = EmptyBag
    /\ snapshotIndex = [n \in Node |-> 0]
    /\ snapshotTerm = [n \in Node |-> 0]
    /\ cfgChangeIndex = [n \in Node |-> -1]

\* Election timeout handler
ElectionTimeout(n) ==
    /\ electionTimer[n] >= electionTimeout[n]
    /\ \/ IsFollower(n)
       \/ IsCandidate(n)
    /\ electionTimer' = [electionTimer EXCEPT ![n] = 0]
    /\ \/ /\ state' = [state EXCEPT ![n] = "PreCandidate"]
          /\ votes' = [votes EXCEPT ![n] = {}]
          /\ \E m \in Node \ {n}:
                messages' = messages \cup {MakeRequestVote(n, m, currentTerm[n] + 1, n, LastLogIndex(n), LastLogTerm(n), TRUE)}
       \/ /\ state' = [state EXCEPT ![n] = "Candidate"]
          /\ currentTerm' = [currentTerm EXCEPT ![n] = currentTerm[n] + 1]
          /\ votedFor' = [votedFor EXCEPT ![n] = n]
          /\ votes' = [votes EXCEPT ![n] = {n}]
          /\ \E m \in Node \ {n}:
                messages' = messages \cup {MakeRequestVote(n, m, currentTerm[n] + 1, n, LastLogIndex(n), LastLogTerm(n), FALSE)}
    /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex, leaderId, snapshotIndex, snapshotTerm, cfgChangeIndex>>

\* RequestVote handler
RecvRequestVote(n, m) ==
    LET msg == CHOOSE msg \in messages: msg.type = "RequestVote" /\ msg.to = n
    IN
    /\ msg.from = m
    /\ \/ /\ msg.prevote
          /\ \/ msg.term > currentTerm[n]
             \/ /\ msg.term = currentTerm[n] + 1
                /\ \/ leaderId[n] = NoNode
                   \/ leaderId[n] = msg.candidateId
          /\ LogUpToDate(n, msg.lastLogIndex, msg.lastLogTerm)
          /\ messages' = messages \cup {MakeRequestVoteResponse(n, m, currentTerm[n], TRUE, msg.term, TRUE)}
       \/ /\ ~msg.prevote
          /\ \/ msg.term > currentTerm[n]
             \/ /\ msg.term = currentTerm[n]
                /\ \/ votedFor[n] = NoNode
                   \/ votedFor[n] = msg.candidateId
          /\ LogUpToDate(n, msg.lastLogIndex, msg.lastLogTerm)
          /\ \/ msg.term > currentTerm[n]
                /\ currentTerm' = [currentTerm EXCEPT ![n] = msg.term]
                /\ votedFor' = [votedFor EXCEPT ![n] = msg.candidateId]
                /\ state' = [state EXCEPT ![n] = "Follower"]
                /\ leaderId' = [leaderId EXCEPT ![n] = NoNode]
             \/ UNCHANGED <<currentTerm, votedFor, state, leaderId>>
          /\ messages' = messages \cup {MakeRequestVoteResponse(n, m, currentTerm[n], TRUE, msg.term, FALSE)}
       \/ /\ messages' = messages \cup {MakeRequestVoteResponse(n, m, currentTerm[n], FALSE, msg.term, msg.prevote)}
          /\ UNCHANGED <<currentTerm, votedFor, state, leaderId>>
    /\ electionTimer' = [electionTimer EXCEPT ![n] = 0]
    /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex, votes, snapshotIndex, snapshotTerm, cfgChangeIndex>>

\* RequestVoteResponse handler
RecvRequestVoteResponse(n, m) ==
    LET msg == CHOOSE msg \in messages: msg.type = "RequestVoteResponse" /\ msg.to = n
    IN
    /\ msg.from = m
    /\ \/ /\ msg.prevote
          /\ IsPreCandidate(n)
          /\ msg.requestTerm = currentTerm[n] + 1
          /\ \/ /\ msg.voteGranted
                /\ votes' = [votes EXCEPT ![n] = votes[n] \cup {m}]
                /\ \/ /\ HasMajorityVotes(n)
                      /\ state' = [state EXCEPT ![n] = "Candidate"]
                      /\ currentTerm' = [currentTerm EXCEPT ![n] = currentTerm[n] + 1]
                      /\ votedFor' = [votedFor EXCEPT ![n] = n]
                      /\ votes' = [votes EXCEPT ![n] = {n}]
                      /\ \E o \in Node \ {n}:
                            messages' = messages \cup {MakeRequestVote(n, o, currentTerm[n] + 1, n, LastLogIndex(n), LastLogTerm(n), FALSE)}
                   \/ UNCHANGED <<state, currentTerm, votedFor, votes, messages>>
             \/ UNCHANGED <<votes>>
          /\ UNCHANGED <<leaderId>>
       \/ /\ ~msg.prevote
          /\ IsCandidate(n)
          /\ msg.requestTerm = currentTerm[n]
          /\ \/ /\ msg.voteGranted
                /\ votes' = [votes EXCEPT ![n] = votes[n] \cup {m}]
                /\ \/ /\ HasMajorityVotes(n)
                      /\ state' = [state EXCEPT ![n] = "Leader"]
                      /\ leaderId' = [leaderId EXCEPT ![n] = n]
                      /\ nextIndex' = [nextIndex EXCEPT ![n] = [o \in Node |-> LastLogIndex(n) + 1]]
                      /\ matchIndex' = [matchIndex EXCEPT ![n] = [o \in Node |-> 0]]
                      /\ \E o \in Node \ {n}:
                            messages' = messages \cup {MakeAppendEntries(n, o, currentTerm[n], LastLogIndex(n), LastLogTerm(n), <<>>, commitIndex[n], 1)}
                   \/ UNCHANGED <<state, leaderId, nextIndex, matchIndex, messages>>
             \/ UNCHANGED <<votes>>
          /\ UNCHANGED <<currentTerm, votedFor>>
    /\ UNCHANGED <<log, commitIndex, lastApplied, snapshotIndex, snapshotTerm, cfgChangeIndex, electionTimer>>

\* AppendEntries handler
RecvAppendEntries(n, m) ==
    LET msg == CHOOSE msg \in messages: msg.type = "AppendEntries" /\ msg.to = n
    IN
    /\ msg.from = m
    /\ \/ /\ msg.term < currentTerm[n]
          /\ messages' = messages \cup {MakeAppendEntriesResponse(n, m, currentTerm[n], FALSE, LastLogIndex(n), msg.msgId)}
       \/ /\ msg.term >= currentTerm[n]
          /\ \/ msg.term > currentTerm[n]
                /\ currentTerm' = [currentTerm EXCEPT ![n] = msg.term]
                /\ votedFor' = [votedFor EXCEPT ![n] = NoNode]
             \/ UNCHANGED <<currentTerm, votedFor>>
          /\ state' = [state EXCEPT ![n] = "Follower"]
          /\ leaderId' = [leaderId EXCEPT ![n] = m]
          /\ electionTimer' = [electionTimer EXCEPT ![n] = 0]
          /\ \/ /\ msg.prevLogIndex = 0
                /\ TRUE
             \/ /\ msg.prevLogIndex > 0
                /\ \/ msg.prevLogIndex > LastLogIndex(n)
                   \/ LogTerm(log[n], msg.prevLogIndex) # msg.prevLogTerm
                /\ messages' = messages \cup {MakeAppendEntriesResponse(n, m, currentTerm[n], FALSE, LastLogIndex(n), msg.msgId)}
             \/ /\ msg.prevLogIndex > 0
                /\ msg.prevLogIndex <= LastLogIndex(n)
                /\ LogTerm(log[n], msg.prevLogIndex) = msg.prevLogTerm
                /\ log' = [log EXCEPT ![n] = 
                       SubSeq(log[n], 1, msg.prevLogIndex) \o msg.entries]
                /\ commitIndex' = [commitIndex EXCEPT ![n] = 
                       IF msg.leaderCommit > commitIndex[n] THEN
                           Min(msg.leaderCommit, LastLogIndex(n))
                       ELSE
                           commitIndex[n]]
                /\ messages' = messages \cup {MakeAppendEntriesResponse(n, m, currentTerm[n], TRUE, LastLogIndex(n), msg.msgId)}
          /\ UNCHANGED <<votes, nextIndex, matchIndex, snapshotIndex, snapshotTerm, cfgChangeIndex>>
    /\ UNCHANGED <<lastApplied>>

\* AppendEntriesResponse handler
RecvAppendEntriesResponse(n, m) ==
    LET msg == CHOOSE msg \in messages: msg.type = "AppendEntriesResponse" /\ msg.to = n
    IN
    /\ msg.from = m
    /\ IsLeader(n)
    /\ \/ /\ msg.term > currentTerm[n]
          /\ currentTerm' = [currentTerm EXCEPT ![n] = msg.term]
          /\ state' = [state EXCEPT ![n] = "Follower"]
          /\ votedFor' = [votedFor EXCEPT ![n] = NoNode]
          /\ leaderId' = [leaderId EXCEPT ![n] = NoNode]
          /\ votes' = [votes EXCEPT ![n] = {}]
       \/ /\ msg.term <= currentTerm[n]
          /\ \/ /\ msg.success
                /\ matchIndex' = [matchIndex EXCEPT ![n][m] = msg.currentIndex]
                /\ nextIndex' = [nextIndex EXCEPT ![n][m] = msg.currentIndex + 1]
                /\ \* Update commit index
                LET N == CHOOSE i \in {commitIndex[n] + 1 .. LastLogIndex(n)}:
                         /\ log[n][i].term = currentTerm[n]
                         /\ Cardinality({o \in Node : matchIndex[n][o] >= i}) >= Majority
                IN
                \/ /\ \E i \in {commitIndex[n] + 1 .. LastLogIndex(n)}:
                         log[n][i].term = currentTerm[n]
                         /\ Cardinality({o \in Node : matchIndex[n][o] >= i}) >= Majority
                    /\ commitIndex' = [commitIndex EXCEPT ![n] = 
                           Max({i \in {commitIndex[n] + 1 .. LastLogIndex(n)}:
                               log[n][i].term = currentTerm[n] /\
                               Cardinality({o \in Node : matchIndex[n][o] >= i}) >= Majority})]
                 \/ UNCHANGED <<commitIndex>>
             \/ /\ ~msg.success
                /\ nextIndex' = [nextIndex EXCEPT ![n][m] = Max({nextIndex[n][m] - 1, 1})]
                /\ UNCHANGED <<commitIndex>>
          /\ UNCHANGED <<currentTerm, state, votedFor, leaderId, votes>>
    /\ UNCHANGED <<log, lastApplied, snapshotIndex, snapshotTerm, cfgChangeIndex, electionTimer>>

\* Leader heartbeat
LeaderHeartbeat(n) ==
    /\ IsLeader(n)
    /\ electionTimer[n] >= 1
    /\ electionTimer' = [electionTimer EXCEPT ![n] = 0]
    /\ \E m \in Node \ {n}:
          LET prevLogIndex == nextIndex[n][m] - 1
          IN
          messages' = messages \cup {MakeAppendEntries(n, m, currentTerm[n], prevLogIndex, 
                                  LogTerm(log[n], prevLogIndex), 
                                  IF nextIndex[n][m] <= LastLogIndex(n) THEN
                                      SubSeq(log[n], nextIndex[n][m], LastLogIndex(n))
                                  ELSE
                                      <<>>,
                                  commitIndex[n], 1)}
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, leaderId, votes, snapshotIndex, snapshotTerm, cfgChangeIndex>>

\* Client request handler
ClientRequest(n) ==
    /\ IsLeader(n)
    /\ \E newEntry \in [term: currentTerm[n], type: "Normal", data: {}]:
          log' = [log EXCEPT ![n] = log[n] \o <<newEntry>>]
          /\ \E m \in Node \ {n}:
                LET prevLogIndex == nextIndex[n][m] - 1
                IN
                messages' = messages \cup {MakeAppendEntries(n, m, currentTerm[n], prevLogIndex, 
                                        LogTerm(log[n], prevLogIndex), 
                                        SubSeq(log[n], nextIndex[n][m], LastLogIndex(n)),
                                        commitIndex[n], 1)}
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, lastApplied, nextIndex, matchIndex, leaderId, electionTimeout, electionTimer, votes, snapshotIndex, snapshotTerm, cfgChangeIndex>>

\* Next state relation
Next ==
    \/ \E n \in Node: ElectionTimeout(n)
    \/ \E n, m \in Node: RecvRequestVote(n, m)
    \/ \E n, m \in Node: RecvRequestVoteResponse(n, m)
    \/ \E n, m \in Node: RecvAppendEntries(n, m)
    \/ \E n, m \in Node: RecvAppendEntriesResponse(n, m)
    \/ \E n \in Node: LeaderHeartbeat(n)
    \/ \E n \in Node: ClientRequest(n)

\* Specification
Spec == Init /\ [][Next]_vars

====