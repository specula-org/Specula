---- MODULE redisraft ----
EXTENDS TLC, Sequences, SequencesExt, Integers, FiniteSets, Bags
CONSTANTS Nodes, NoLeader, None, Follower, PreCandidate, Candidate, Leader
VARIABLES state, currentTerm, votedFor, leaderId, commitIndex, lastApplied, nextIndex, matchIndex, raftLog, electionTimeout, timeoutElapsed, votes, snapshotIndex, snapshotTerm, config, messages
(* Minimal fix: Added missing state constants Follower, PreCandidate, Candidate, Leader *)
(* Minimal fix: Renamed 'log' variable to 'raftLog' to avoid conflict with Sequences module *)
(* Minimal fix: Changed parameter name in LastTerm to avoid conflict with global variable *)
LastTerm(logSeq) == IF Len(logSeq) > 0 THEN logSeq[Len(logSeq)].term ELSE 0
vars == <<state, currentTerm, votedFor, leaderId, commitIndex, lastApplied, nextIndex, matchIndex, raftLog, electionTimeout, timeoutElapsed, votes, snapshotIndex, snapshotTerm, config, messages>>
Init ==
    /\ state = [n \in Nodes |-> Follower]
    /\ currentTerm = [n \in Nodes |-> 0]
    /\ votedFor = [n \in Nodes |-> None]
    /\ leaderId = [n \in Nodes |-> NoLeader]
    /\ commitIndex = [n \in Nodes |-> 0]
    /\ lastApplied = [n \in Nodes |-> 0]
    /\ nextIndex = [n \in Nodes |-> [m \in Nodes |-> 1]]
    /\ matchIndex = [n \in Nodes |-> [m \in Nodes |-> 0]]
    /\ raftLog = <<>>
    /\ electionTimeout = [n \in Nodes |-> 1000]
    /\ timeoutElapsed = [n \in Nodes |-> 0]
    /\ votes = [n \in Nodes |-> {}]
    /\ snapshotIndex = [n \in Nodes |-> 0]
    /\ snapshotTerm = [n \in Nodes |-> 0]
    /\ config = Nodes
    /\ messages = EmptyBag
BecomeFollower(n) ==
    /\ state[n] /= Follower
    /\ state' = [state EXCEPT ![n] = Follower]
    /\ leaderId' = [leaderId EXCEPT ![n] = NoLeader]
    /\ votedFor' = [votedFor EXCEPT ![n] = None]
    /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![n] = 0]
    /\ UNCHANGED <<currentTerm, commitIndex, lastApplied, nextIndex, matchIndex, raftLog, electionTimeout, votes, snapshotIndex, snapshotTerm, config, messages>>
BecomePreCandidate(n) ==
    /\ state[n] = Follower
    /\ timeoutElapsed[n] >= electionTimeout[n]
    /\ state' = [state EXCEPT ![n] = PreCandidate]
    /\ votes' = [votes EXCEPT ![n] = {}]
    /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![n] = 0]
    /\ messages' = messages \cup {[type |-> "RequestVote", from |-> n, to |-> m, term |-> currentTerm[n] + 1, prevote |-> TRUE] : m \in config \ {n}}
    /\ UNCHANGED <<currentTerm, votedFor, leaderId, commitIndex, lastApplied, nextIndex, matchIndex, raftLog, electionTimeout, snapshotIndex, snapshotTerm, config>>
BecomeCandidate(n) ==
    /\ state[n] \in {Follower, PreCandidate}
    /\ state' = [state EXCEPT ![n] = Candidate]
    /\ currentTerm' = [currentTerm EXCEPT ![n] = currentTerm[n] + 1]
    /\ votedFor' = [votedFor EXCEPT ![n] = n]
    /\ votes' = [votes EXCEPT ![n] = {n}]
    /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![n] = 0]
    /\ messages' = messages \cup {[type |-> "RequestVote", from |-> n, to |-> m, term |-> currentTerm[n] + 1, prevote |-> FALSE] : m \in config \ {n}}
    /\ UNCHANGED <<leaderId, commitIndex, lastApplied, nextIndex, matchIndex, raftLog, electionTimeout, snapshotIndex, snapshotTerm, config>>
BecomeLeader(n) ==
    /\ state[n] = Candidate
    /\ Cardinality(votes[n]) > Cardinality(config) \div 2
    /\ state' = [state EXCEPT ![n] = Leader]
    /\ leaderId' = [leaderId EXCEPT ![n] = n]
    /\ nextIndex' = [nextIndex EXCEPT ![n] = [m \in config |-> Len(raftLog) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![n] = [m \in config |-> 0]]
    /\ raftLog' = Append(raftLog, [term |-> currentTerm[n], data |-> "noop"])
    /\ messages' = messages \cup {[type |-> "AppendEntries", from |-> n, to |-> m, term |-> currentTerm[n], leaderCommit |-> commitIndex[n]] : m \in config \ {n}}
    /\ UNCHANGED <<currentTerm, votedFor, commitIndex, lastApplied, electionTimeout, timeoutElapsed, votes, snapshotIndex, snapshotTerm, config>>
RecvRequestVote(n, m) ==
    /\ m \in messages
    /\ m.type = "RequestVote"
    /\ m.to = n
    /\ \/ (m.term > currentTerm[n]) /\ BecomeFollower(n)
       \/ (m.term <= currentTerm[n]) /\ UNCHANGED state
    /\ LET
        grantVote ==
            /\ votedFor[n] \in {None, m.from}
            /\ m.lastLogTerm >= LastTerm(raftLog)
            /\ m.lastLogIndex >= Len(raftLog)
       IN
        IF grantVote THEN
            /\ votedFor' = [votedFor EXCEPT ![n] = m.from]
            /\ messages' = messages \cup {[type |-> "RequestVoteResponse", from |-> n, to |-> m.from, term |-> currentTerm[n], voteGranted |-> TRUE, requestTerm |-> m.term]}
        ELSE
            /\ messages' = messages \cup {[type |-> "RequestVoteResponse", from |-> n, to |-> m.from, term |-> currentTerm[n], voteGranted |-> FALSE, requestTerm |-> m.term]}
    /\ UNCHANGED <<state, currentTerm, leaderId, commitIndex, lastApplied, nextIndex, matchIndex, raftLog, electionTimeout, timeoutElapsed, votes, snapshotIndex, snapshotTerm, config>>
RecvRequestVoteResponse(n, m) ==
    /\ m \in messages
    /\ m.type = "RequestVoteResponse"
    /\ m.to = n
    /\ m.requestTerm = currentTerm[n] + IF state[n] = PreCandidate THEN 1 ELSE 0
    /\ IF m.voteGranted THEN
           votes' = [votes EXCEPT ![n] = votes[n] \cup {m.from}]
       ELSE
           UNCHANGED votes
    /\ IF Cardinality(votes'[n]) > Cardinality(config) \div 2 THEN
           IF state[n] = PreCandidate THEN BecomeCandidate(n) ELSE BecomeLeader(n)
       ELSE
           UNCHANGED state
    /\ messages' = messages \ {m}
    /\ UNCHANGED <<currentTerm, votedFor, leaderId, commitIndex, lastApplied, nextIndex, matchIndex, raftLog, electionTimeout, timeoutElapsed, snapshotIndex, snapshotTerm, config>>
RecvAppendEntries(n, m) ==
    /\ m \in messages
    /\ m.type = "AppendEntries"
    /\ m.to = n
    /\ \/ (m.term > currentTerm[n]) /\ BecomeFollower(n)
       \/ (m.term <= currentTerm[n]) /\ UNCHANGED state
    /\ IF m.term >= currentTerm[n] THEN
           /\ leaderId' = [leaderId EXCEPT ![n] = m.from]
           /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![n] = 0]
       ELSE UNCHANGED <<leaderId, timeoutElapsed>>
    /\ LET
        logOk ==
            \/ m.prevLogIndex = 0
            \/ (m.prevLogIndex <= Len(raftLog)) /\ (m.prevLogTerm = raftLog[m.prevLogIndex].term)
       IN
        IF logOk THEN
            (* Minimal fix: Changed MIN to Min *)
            /\ commitIndex' = [commitIndex EXCEPT ![n] = Min(m.leaderCommit, Len(raftLog) + Len(m.entries))]
            /\ messages' = messages \cup {[type |-> "AppendEntriesResponse", from |-> n, to |-> m.from, term |-> currentTerm[n], success |-> TRUE, matchIndex |-> m.prevLogIndex + Len(m.entries)]}
        ELSE
            /\ messages' = messages \cup {[type |-> "AppendEntriesResponse", from |-> n, to |-> m.from, term |-> currentTerm[n], success |-> FALSE, matchIndex |-> Len(raftLog)]}
    /\ UNCHANGED <<state, currentTerm, votedFor, nextIndex, matchIndex, raftLog, electionTimeout, votes, snapshotIndex, snapshotTerm, config>>
RecvAppendEntriesResponse(n, m) ==
    /\ m \in messages
    /\ m.type = "AppendEntriesResponse"
    /\ m.to = n
    /\ state[n] = Leader
    /\ IF m.term > currentTerm[n] THEN
           BecomeFollower(n)
       ELSE
           UNCHANGED state
    /\ IF m.success THEN
           /\ nextIndex' = [nextIndex EXCEPT ![n][m.from] = m.matchIndex + 1]
           /\ matchIndex' = [matchIndex EXCEPT ![n][m.from] = m.matchIndex]
           /\ LET
                N == CHOOSE k \in {i \in 1..Len(raftLog) : raftLog[i].term = currentTerm[n]} :
                    Cardinality({node \in config : matchIndex[n][node] >= k}) > Cardinality(config) \div 2
              IN
                IF N > commitIndex[n] THEN
                    commitIndex' = [commitIndex EXCEPT ![n] = N]
                ELSE
                    UNCHANGED commitIndex
       ELSE
           (* Minimal fix: Changed MAX to Max *)
           /\ nextIndex' = [nextIndex EXCEPT ![n][m.from] = Max(1, nextIndex[n][m.from] - 1)]
           /\ UNCHANGED matchIndex
    /\ messages' = messages \ {m}
    /\ UNCHANGED <<currentTerm, votedFor, leaderId, lastApplied, raftLog, electionTimeout, timeoutElapsed, votes, snapshotIndex, snapshotTerm, config>>
SendAppendEntries(n, to) ==
    /\ state[n] = Leader
    /\ nextIndex[n][to] <= Len(raftLog)
    /\ messages' = messages \cup {[type |-> "AppendEntries", from |-> n, to |-> to, term |-> currentTerm[n], prevLogIndex |-> nextIndex[n][to] - 1, prevLogTerm |-> raftLog[nextIndex[n][to] - 1].term, entries |-> SubSeq(raftLog, nextIndex[n][to], Len(raftLog)), leaderCommit |-> commitIndex[n]]}
    /\ UNCHANGED <<state, currentTerm, votedFor, leaderId, commitIndex, lastApplied, nextIndex, matchIndex, raftLog, electionTimeout, timeoutElapsed, votes, snapshotIndex, snapshotTerm, config>>
SendHeartbeat(n) ==
    /\ state[n] = Leader
    /\ messages' = messages \cup {[type |-> "AppendEntries", from |-> n, to |-> m, term |-> currentTerm[n], prevLogIndex |-> Len(raftLog), prevLogTerm |-> LastTerm(raftLog), entries |-> <<>>, leaderCommit |-> commitIndex[n]] : m \in config \ {n}}
    /\ UNCHANGED <<state, currentTerm, votedFor, leaderId, commitIndex, lastApplied, nextIndex, matchIndex, raftLog, electionTimeout, timeoutElapsed, votes, snapshotIndex, snapshotTerm, config>>
ElectionStart(n) ==
    /\ state[n] = Follower
    /\ timeoutElapsed[n] >= electionTimeout[n]
    /\ BecomePreCandidate(n)
ElectionTimeout(n) ==
    /\ state[n] \in {Follower, Candidate}
    /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![n] = @ + 1]
    /\ UNCHANGED <<state, currentTerm, votedFor, leaderId, commitIndex, lastApplied, nextIndex, matchIndex, raftLog, electionTimeout, votes, snapshotIndex, snapshotTerm, config, messages>>
LogAppend(n, entry) ==
    /\ state[n] = Leader
    /\ raftLog' = Append(raftLog, [term |-> currentTerm[n], data |-> entry])
    /\ UNCHANGED <<state, currentTerm, votedFor, leaderId, commitIndex, lastApplied, nextIndex, matchIndex, electionTimeout, timeoutElapsed, votes, snapshotIndex, snapshotTerm, config, messages>>
LogDelete(n, index) ==
    /\ index > commitIndex[n]
    /\ raftLog' = SubSeq(raftLog, 1, index - 1)
    /\ UNCHANGED <<state, currentTerm, votedFor, leaderId, commitIndex, lastApplied, nextIndex, matchIndex, electionTimeout, timeoutElapsed, votes, snapshotIndex, snapshotTerm, config, messages>>
LogCommit(n) ==
    /\ lastApplied[n] < commitIndex[n]
    /\ lastApplied' = [lastApplied EXCEPT ![n] = lastApplied[n] + 1]
    /\ UNCHANGED <<state, currentTerm, votedFor, leaderId, commitIndex, nextIndex, matchIndex, raftLog, electionTimeout, timeoutElapsed, votes, snapshotIndex, snapshotTerm, config, messages>>
PeriodicElectionTimeout(n) ==
    ElectionTimeout(n)
PeriodicHeartbeat(n) ==
    SendHeartbeat(n)
AddNode(n, newNode) ==
    /\ newNode \notin config
    /\ config' = config \cup {newNode}
    (* Minimal fix: Added LET to handle complex EXCEPT expressions *)
    /\ LET newNextIndex == [nextIndex[n] @@ [newNode |-> Len(raftLog) + 1]] IN
        nextIndex' = [nextIndex EXCEPT ![n] = newNextIndex]
    /\ LET newMatchIndex == [matchIndex[n] @@ [newNode |-> 0]] IN
        matchIndex' = [matchIndex EXCEPT ![n] = newMatchIndex]
    /\ UNCHANGED <<state, currentTerm, votedFor, leaderId, commitIndex, lastApplied, raftLog, electionTimeout, timeoutElapsed, votes, snapshotIndex, snapshotTerm, messages>>
RemoveNode(n, nodeToRemove) ==
    /\ nodeToRemove \in config
    /\ config' = config \ {nodeToRemove}
    /\ nextIndex' = [nextIndex EXCEPT ![n] = [m \in config' |-> nextIndex[n][m]]]
    /\ matchIndex' = [matchIndex EXCEPT ![n] = [m \in config' |-> matchIndex[n][m]]]
    /\ UNCHANGED <<state, currentTerm, votedFor, leaderId, commitIndex, lastApplied, raftLog, electionTimeout, timeoutElapsed, votes, snapshotIndex, snapshotTerm, messages>>
SnapshotBegin(n) ==
    /\ commitIndex[n] > snapshotIndex[n]
    /\ snapshotIndex' = [snapshotIndex EXCEPT ![n] = commitIndex[n]]
    /\ snapshotTerm' = [snapshotTerm EXCEPT ![n] = raftLog[commitIndex[n]].term]
    /\ UNCHANGED <<state, currentTerm, votedFor, leaderId, commitIndex, lastApplied, nextIndex, matchIndex, raftLog, electionTimeout, timeoutElapsed, votes, config, messages>>
SnapshotEnd(n) ==
    /\ snapshotIndex[n] > 0
    /\ raftLog' = SubSeq(raftLog, snapshotIndex[n] + 1, Len(raftLog))
    /\ UNCHANGED <<state, currentTerm, votedFor, leaderId, commitIndex, lastApplied, nextIndex, matchIndex, electionTimeout, timeoutElapsed, votes, snapshotIndex, snapshotTerm, config, messages>>
ApplyConfigChange(n, newConfig) ==
    /\ newConfig \subseteq Nodes
    /\ config' = newConfig
    /\ UNCHANGED <<state, currentTerm, votedFor, leaderId, commitIndex, lastApplied, nextIndex, matchIndex, raftLog, electionTimeout, timeoutElapsed, votes, snapshotIndex, snapshotTerm, messages>>
Next ==
    \/ \E n \in Nodes: BecomeFollower(n)
    \/ \E n \in Nodes: BecomePreCandidate(n)
    \/ \E n \in Nodes: BecomeCandidate(n)
    \/ \E n \in Nodes: BecomeLeader(n)
    \/ \E n \in Nodes, m \in messages: RecvRequestVote(n, m)
    \/ \E n \in Nodes, m \in messages: RecvRequestVoteResponse(n, m)
    \/ \E n \in Nodes, m \in messages: RecvAppendEntries(n, m)
    \/ \E n \in Nodes, m \in messages: RecvAppendEntriesResponse(n, m)
    \/ \E n \in Nodes, to \in config \ {n}: SendAppendEntries(n, to)
    \/ \E n \in Nodes: SendHeartbeat(n)
    \/ \E n \in Nodes: ElectionStart(n)
    \/ \E n \in Nodes: ElectionTimeout(n)
    \/ \E n \in Nodes, entry \in {"data1", "data2"}: LogAppend(n, entry)
    \/ \E n \in Nodes, idx \in 1..Len(raftLog): LogDelete(n, idx)
    \/ \E n \in Nodes: LogCommit(n)
    \/ \E n \in Nodes: PeriodicElectionTimeout(n)
    \/ \E n \in Nodes: PeriodicHeartbeat(n)
    \/ \E n \in Nodes, newNode \in Nodes \ config: AddNode(n, newNode)
    \/ \E n \in Nodes, nodeToRemove \in config: RemoveNode(n, nodeToRemove)
    \/ \E n \in Nodes: SnapshotBegin(n)
    \/ \E n \in Nodes: SnapshotEnd(n)
    (* Minimal fix: Split complex quantifier into nested quantifiers *)
    \/ \E n \in Nodes: \E newConfig \in SUBSET Nodes: ApplyConfigChange(n, newConfig)
Spec == Init /\ [][Next]_vars
====