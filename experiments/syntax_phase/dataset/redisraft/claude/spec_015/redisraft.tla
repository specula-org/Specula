---- MODULE redisraft ----

EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags, Integers

CONSTANTS Nodes, MaxTerm, MaxLogLen, MaxMsgId

VARIABLES
    state,           
    currentTerm,     
    votedFor,        
    log,             
    commitIndex,     
    lastApplied,     
    nextIndex,       
    matchIndex,      
    votes,           
    electionTimeout, 
    heartbeatTimeout,
    messages,        
    msgId,           
    snapshotIndex,   
    snapshotTerm,    
    snapshotInProgress,
    nodeConfig,      
    configChangeInProgress

NodeStates == {"FOLLOWER", "PRECANDIDATE", "CANDIDATE", "LEADER"}
MessageTypes == {"RequestVote", "RequestVoteResponse", "AppendEntries", "AppendEntriesResponse", "Snapshot", "SnapshotResponse", "TimeoutNow"}
LogEntryTypes == {"Normal", "AddNode", "RemoveNode", "AddNonVotingNode", "NoOp"}

vars == <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, votes, electionTimeout, heartbeatTimeout, messages, msgId, snapshotIndex, snapshotTerm, snapshotInProgress, nodeConfig, configChangeInProgress>>

Min(a, b) == IF a <= b THEN a ELSE b
Max(a, b) == IF a >= b THEN a ELSE b

SetToSeq(S) == 
    LET f[s \in SUBSET S] == 
        IF s = {} THEN <<>>
        ELSE LET x == CHOOSE y \in s : TRUE
             IN <<x>> \o f[s \ {x}]
    IN f[S]

SortSeq(seq, comp) ==
    LET Merge(left, right) ==
        LET MergeHelper[l \in Seq(UNION Range(seq)), r \in Seq(UNION Range(seq))] ==
            IF l = <<>> THEN r
            ELSE IF r = <<>> THEN l
            ELSE IF comp(Head(l), Head(r)) THEN <<Head(l)>> \o MergeHelper[Tail(l), r]
            ELSE <<Head(r)>> \o MergeHelper[l, Tail(r)]
        IN MergeHelper[left, right]
    IN IF Len(seq) <= 1 THEN seq
       ELSE LET mid == Len(seq) \div 2
                left == SubSeq(seq, 1, mid)
                right == SubSeq(seq, mid + 1, Len(seq))
            IN Merge(SortSeq(left, comp), SortSeq(right, comp))

Init ==
    /\ state = [n \in Nodes |-> "FOLLOWER"]
    /\ currentTerm = [n \in Nodes |-> 0]
    /\ votedFor = [n \in Nodes |-> "none"]
    /\ log = [n \in Nodes |-> <<>>]
    /\ commitIndex = [n \in Nodes |-> 0]
    /\ lastApplied = [n \in Nodes |-> 0]
    /\ nextIndex = [n \in Nodes |-> [m \in Nodes |-> 1]]
    /\ matchIndex = [n \in Nodes |-> [m \in Nodes |-> 0]]
    /\ votes = [n \in Nodes |-> {}]
    /\ electionTimeout = [n \in Nodes |-> FALSE]
    /\ heartbeatTimeout = [n \in Nodes |-> FALSE]
    /\ messages = {}
    /\ msgId = [n \in Nodes |-> 0]
    /\ snapshotIndex = [n \in Nodes |-> 0]
    /\ snapshotTerm = [n \in Nodes |-> 0]
    /\ snapshotInProgress = [n \in Nodes |-> FALSE]
    /\ nodeConfig = [n \in Nodes |-> [voting |-> TRUE, active |-> TRUE]]
    /\ configChangeInProgress = [n \in Nodes |-> FALSE]

VotingNodes == {n \in Nodes : nodeConfig[n].voting /\ nodeConfig[n].active}
Majority(S) == Cardinality(S) * 2 > Cardinality(VotingNodes)

BecomeFollower(n) ==
    /\ state' = [state EXCEPT ![n] = "FOLLOWER"]
    /\ votedFor' = [votedFor EXCEPT ![n] = "none"]
    /\ votes' = [votes EXCEPT ![n] = {}]
    /\ electionTimeout' = [electionTimeout EXCEPT ![n] = FALSE]
    /\ UNCHANGED <<currentTerm, log, commitIndex, lastApplied, nextIndex, matchIndex, heartbeatTimeout, messages, msgId, snapshotIndex, snapshotTerm, snapshotInProgress, nodeConfig, configChangeInProgress>>

BecomePreCandidate(n) ==
    /\ state[n] = "FOLLOWER"
    /\ electionTimeout[n] = TRUE
    /\ state' = [state EXCEPT ![n] = "PRECANDIDATE"]
    /\ votes' = [votes EXCEPT ![n] = {n}]
    /\ electionTimeout' = [electionTimeout EXCEPT ![n] = FALSE]
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, heartbeatTimeout, messages, msgId, snapshotIndex, snapshotTerm, snapshotInProgress, nodeConfig, configChangeInProgress>>

BecomeCandidate(n) ==
    /\ \/ /\ state[n] = "FOLLOWER"
          /\ electionTimeout[n] = TRUE
       \/ /\ state[n] = "PRECANDIDATE"
          /\ Majority(votes[n])
    /\ currentTerm[n] < MaxTerm
    /\ currentTerm' = [currentTerm EXCEPT ![n] = currentTerm[n] + 1]
    /\ state' = [state EXCEPT ![n] = "CANDIDATE"]
    /\ votedFor' = [votedFor EXCEPT ![n] = n]
    /\ votes' = [votes EXCEPT ![n] = {n}]
    /\ electionTimeout' = [electionTimeout EXCEPT ![n] = FALSE]
    /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex, heartbeatTimeout, messages, msgId, snapshotIndex, snapshotTerm, snapshotInProgress, nodeConfig, configChangeInProgress>>

BecomeLeader(n) ==
    /\ state[n] = "CANDIDATE"
    /\ Majority(votes[n])
    /\ Len(log[n]) < MaxLogLen
    /\ state' = [state EXCEPT ![n] = "LEADER"]
    /\ nextIndex' = [nextIndex EXCEPT ![n] = [m \in Nodes |-> Len(log[n]) + 2]]
    /\ matchIndex' = [matchIndex EXCEPT ![n] = [m \in Nodes |-> IF m = n THEN Len(log[n]) + 1 ELSE 0]]
    /\ heartbeatTimeout' = [heartbeatTimeout EXCEPT ![n] = TRUE]
    /\ log' = [log EXCEPT ![n] = Append(log[n], [term |-> currentTerm[n], type |-> "NoOp", data |-> ""])]
    /\ UNCHANGED <<currentTerm, votedFor, commitIndex, lastApplied, votes, electionTimeout, messages, msgId, snapshotIndex, snapshotTerm, snapshotInProgress, nodeConfig, configChangeInProgress>>

ElectionStart(n) ==
    /\ state[n] = "FOLLOWER"
    /\ electionTimeout[n] = TRUE
    /\ BecomePreCandidate(n)

ElectionTimeout(n) ==
    /\ electionTimeout[n] = FALSE
    /\ electionTimeout' = [electionTimeout EXCEPT ![n] = TRUE]
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, votes, heartbeatTimeout, messages, msgId, snapshotIndex, snapshotTerm, snapshotInProgress, nodeConfig, configChangeInProgress>>

PeriodicElectionTimeout(n) ==
    /\ state[n] \in {"FOLLOWER", "PRECANDIDATE", "CANDIDATE"}
    /\ ElectionTimeout(n)

PeriodicHeartbeat(n) ==
    /\ state[n] = "LEADER"
    /\ heartbeatTimeout[n] = FALSE
    /\ heartbeatTimeout' = [heartbeatTimeout EXCEPT ![n] = TRUE]
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, votes, electionTimeout, messages, msgId, snapshotIndex, snapshotTerm, snapshotInProgress, nodeConfig, configChangeInProgress>>

SendRequestVote(n, m) ==
    /\ state[n] \in {"PRECANDIDATE", "CANDIDATE"}
    /\ n # m
    /\ nodeConfig[m].voting
    /\ nodeConfig[m].active
    /\ msgId[n] < MaxMsgId
    /\ LET msg == [type |-> "RequestVote",
                   src |-> n,
                   dst |-> m,
                   term |-> IF state[n] = "PRECANDIDATE" THEN currentTerm[n] + 1 ELSE currentTerm[n],
                   prevote |-> state[n] = "PRECANDIDATE",
                   candidateId |-> n,
                   lastLogIndex |-> Len(log[n]),
                   lastLogTerm |-> IF Len(log[n]) > 0 THEN log[n][Len(log[n])].term ELSE 0,
                   id |-> msgId[n] + 1]
       IN /\ messages' = messages \cup {msg}
          /\ msgId' = [msgId EXCEPT ![n] = msgId[n] + 1]
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, votes, electionTimeout, heartbeatTimeout, snapshotIndex, snapshotTerm, snapshotInProgress, nodeConfig, configChangeInProgress>>

RecvRequestVote(m) ==
    /\ \E msg \in messages :
        /\ msg.type = "RequestVote"
        /\ msg.dst = m
        /\ LET n == msg.src
               voteGranted == /\ msg.term >= currentTerm[m]
                             /\ (votedFor[m] = "none" \/ votedFor[m] = n \/ msg.prevote)
                             /\ LET lastLogTerm == IF Len(log[m]) > 0 THEN log[m][Len(log[m])].term ELSE 0
                                IN \/ msg.lastLogTerm > lastLogTerm
                                   \/ /\ msg.lastLogTerm = lastLogTerm
                                      /\ msg.lastLogIndex >= Len(log[m])
               response == [type |-> "RequestVoteResponse",
                           src |-> m,
                           dst |-> n,
                           term |-> currentTerm[m],
                           voteGranted |-> voteGranted,
                           prevote |-> msg.prevote,
                           id |-> msg.id]
           IN /\ IF msg.term > currentTerm[m] /\ ~msg.prevote
                 THEN /\ currentTerm' = [currentTerm EXCEPT ![m] = msg.term]
                      /\ state' = [state EXCEPT ![m] = "FOLLOWER"]
                      /\ votedFor' = [votedFor EXCEPT ![m] = IF voteGranted THEN n ELSE "none"]
                 ELSE /\ IF voteGranted /\ ~msg.prevote
                         THEN votedFor' = [votedFor EXCEPT ![m] = n]
                         ELSE UNCHANGED votedFor
                      /\ UNCHANGED <<currentTerm, state>>
              /\ messages' = (messages \ {msg}) \cup {response}
              /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex, votes, electionTimeout, heartbeatTimeout, msgId, snapshotIndex, snapshotTerm, snapshotInProgress, nodeConfig, configChangeInProgress>>

RecvRequestVoteResponse(n) ==
    /\ \E msg \in messages :
        /\ msg.type = "RequestVoteResponse"
        /\ msg.dst = n
        /\ state[n] \in {"PRECANDIDATE", "CANDIDATE"}
        /\ LET m == msg.src
           IN /\ IF msg.term > currentTerm[n]
                 THEN /\ currentTerm' = [currentTerm EXCEPT ![n] = msg.term]
                      /\ state' = [state EXCEPT ![n] = "FOLLOWER"]
                      /\ votedFor' = [votedFor EXCEPT ![n] = "none"]
                      /\ votes' = [votes EXCEPT ![n] = {}]
                 ELSE /\ IF msg.voteGranted
                         THEN votes' = [votes EXCEPT ![n] = votes[n] \cup {m}]
                         ELSE UNCHANGED votes
                      /\ UNCHANGED <<currentTerm, state, votedFor>>
              /\ messages' = messages \ {msg}
              /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex, electionTimeout, heartbeatTimeout, msgId, snapshotIndex, snapshotTerm, snapshotInProgress, nodeConfig, configChangeInProgress>>

SendAppendEntries(n, m) ==
    /\ state[n] = "LEADER"
    /\ n # m
    /\ nodeConfig[m].active
    /\ msgId[n] < MaxMsgId
    /\ LET prevLogIndex == nextIndex[n][m] - 1
           prevLogTerm == IF prevLogIndex > 0 /\ prevLogIndex <= Len(log[n])
                         THEN log[n][prevLogIndex].term
                         ELSE IF prevLogIndex = snapshotIndex[n]
                         THEN snapshotTerm[n]
                         ELSE 0
           entries == IF nextIndex[n][m] <= Len(log[n])
                     THEN SubSeq(log[n], nextIndex[n][m], Len(log[n]))
                     ELSE <<>>
           msg == [type |-> "AppendEntries",
                   src |-> n,
                   dst |-> m,
                   term |-> currentTerm[n],
                   leaderId |-> n,
                   prevLogIndex |-> prevLogIndex,
                   prevLogTerm |-> prevLogTerm,
                   entries |-> entries,
                   leaderCommit |-> commitIndex[n],
                   id |-> msgId[n] + 1]
       IN /\ messages' = messages \cup {msg}
          /\ msgId' = [msgId EXCEPT ![n] = msgId[n] + 1]
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, votes, electionTimeout, heartbeatTimeout, snapshotIndex, snapshotTerm, snapshotInProgress, nodeConfig, configChangeInProgress>>

SendHeartbeat(n) ==
    /\ state[n] = "LEADER"
    /\ heartbeatTimeout[n] = TRUE
    /\ \E m \in Nodes : m # n /\ nodeConfig[m].active /\ SendAppendEntries(n, m)
    /\ heartbeatTimeout' = [heartbeatTimeout EXCEPT ![n] = FALSE]

RecvAppendEntries(m) ==
    /\ \E msg \in messages :
        /\ msg.type = "AppendEntries"
        /\ msg.dst = m
        /\ LET n == msg.src
               success == /\ msg.term >= currentTerm[m]
                         /\ \/ msg.prevLogIndex = 0
                            \/ /\ msg.prevLogIndex <= Len(log[m])
                               /\ log[m][msg.prevLogIndex].term = msg.prevLogTerm
                            \/ /\ msg.prevLogIndex = snapshotIndex[m]
                               /\ msg.prevLogTerm = snapshotTerm[m]
               response == [type |-> "AppendEntriesResponse",
                           src |-> m,
                           dst |-> n,
                           term |-> currentTerm[m],
                           success |-> success,
                           matchIndex |-> IF success THEN msg.prevLogIndex + Len(msg.entries) ELSE Len(log[m]),
                           id |-> msg.id]
           IN /\ IF msg.term > currentTerm[m]
                 THEN /\ currentTerm' = [currentTerm EXCEPT ![m] = msg.term]
                      /\ state' = [state EXCEPT ![m] = "FOLLOWER"]
                      /\ votedFor' = [votedFor EXCEPT ![m] = "none"]
                 ELSE UNCHANGED <<currentTerm, state, votedFor>>
              /\ IF success /\ Len(msg.entries) > 0
                 THEN log' = [log EXCEPT ![m] = SubSeq(log[m], 1, msg.prevLogIndex) \o msg.entries]
                 ELSE UNCHANGED log
              /\ IF success /\ msg.leaderCommit > commitIndex[m]
                 THEN commitIndex' = [commitIndex EXCEPT ![m] = Min(msg.leaderCommit, Len(log'[m]))]
                 ELSE UNCHANGED commitIndex
              /\ messages' = (messages \ {msg}) \cup {response}
              /\ electionTimeout' = [electionTimeout EXCEPT ![m] = FALSE]
              /\ UNCHANGED <<lastApplied, nextIndex, matchIndex, votes, heartbeatTimeout, msgId, snapshotIndex, snapshotTerm, snapshotInProgress, nodeConfig, configChangeInProgress>>

RecvAppendEntriesResponse(n) ==
    /\ \E msg \in messages :
        /\ msg.type = "AppendEntriesResponse"
        /\ msg.dst = n
        /\ state[n] = "LEADER"
        /\ LET m == msg.src
           IN /\ IF msg.term > currentTerm[n]
                 THEN /\ currentTerm' = [currentTerm EXCEPT ![n] = msg.term]
                      /\ state' = [state EXCEPT ![n] = "FOLLOWER"]
                      /\ votedFor' = [votedFor EXCEPT ![n] = "none"]
                 ELSE /\ IF msg.success
                         THEN /\ nextIndex' = [nextIndex EXCEPT ![n] = [nextIndex[n] EXCEPT ![m] = msg.matchIndex + 1]]
                              /\ matchIndex' = [matchIndex EXCEPT ![n] = [matchIndex[n] EXCEPT ![m] = msg.matchIndex]]
                         ELSE /\ nextIndex' = [nextIndex EXCEPT ![n] = [nextIndex[n] EXCEPT ![m] = Max(1, nextIndex[n][m] - 1)]]
                              /\ UNCHANGED matchIndex
                      /\ UNCHANGED <<currentTerm, state, votedFor>>
              /\ messages' = messages \ {msg}
              /\ UNCHANGED <<log, commitIndex, lastApplied, votes, electionTimeout, heartbeatTimeout, msgId, snapshotIndex, snapshotTerm, snapshotInProgress, nodeConfig, configChangeInProgress>>

LogAppend(n, entry) ==
    /\ state[n] = "LEADER"
    /\ Len(log[n]) < MaxLogLen
    /\ log' = [log EXCEPT ![n] = Append(log[n], [term |-> currentTerm[n], type |-> entry.type, data |-> entry.data])]
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, lastApplied, nextIndex, matchIndex, votes, electionTimeout, heartbeatTimeout, messages, msgId, snapshotIndex, snapshotTerm, snapshotInProgress, nodeConfig, configChangeInProgress>>

LogDelete(n, index) ==
    /\ index > commitIndex[n]
    /\ index <= Len(log[n])
    /\ log' = [log EXCEPT ![n] = SubSeq(log[n], 1, index - 1)]
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, lastApplied, nextIndex, matchIndex, votes, electionTimeout, heartbeatTimeout, messages, msgId, snapshotIndex, snapshotTerm, snapshotInProgress, nodeConfig, configChangeInProgress>>

LogCommit(n) ==
    /\ state[n] = "LEADER"
    /\ LET indices == {matchIndex[n][m] : m \in VotingNodes}
           sortedSeq == SortSeq(SetToSeq(indices), LAMBDA x, y : x >= y)
           majorityIndex == IF Len(sortedSeq) > 0 THEN sortedSeq[(Cardinality(VotingNodes) \div 2) + 1] ELSE 0
       IN /\ majorityIndex > commitIndex[n]
          /\ majorityIndex <= Len(log[n])
          /\ majorityIndex > 0
          /\ log[n][majorityIndex].term = currentTerm[n]
          /\ commitIndex' = [commitIndex EXCEPT ![n] = majorityIndex]
    /\ UNCHANGED <<state, currentTerm, votedFor, log, lastApplied, nextIndex, matchIndex, votes, electionTimeout, heartbeatTimeout, messages, msgId, snapshotIndex, snapshotTerm, snapshotInProgress, nodeConfig, configChangeInProgress>>

AddNode(n, newNode) ==
    /\ state[n] = "LEADER"
    /\ newNode \in Nodes
    /\ ~configChangeInProgress[n]
    /\ Len(log[n]) < MaxLogLen
    /\ log' = [log EXCEPT ![n] = Append(log[n], [term |-> currentTerm[n], type |-> "AddNode", data |-> newNode])]
    /\ configChangeInProgress' = [configChangeInProgress EXCEPT ![n] = TRUE]
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, lastApplied, nextIndex, matchIndex, votes, electionTimeout, heartbeatTimeout, messages, msgId, snapshotIndex, snapshotTerm, snapshotInProgress, nodeConfig>>

RemoveNode(n, oldNode) ==
    /\ state[n] = "LEADER"
    /\ oldNode \in Nodes
    /\ oldNode # n
    /\ ~configChangeInProgress[n]
    /\ Len(log[n]) < MaxLogLen
    /\ log' = [log EXCEPT ![n] = Append(log[n], [term |-> currentTerm[n], type |-> "RemoveNode", data |-> oldNode])]
    /\ configChangeInProgress' = [configChangeInProgress EXCEPT ![n] = TRUE]
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, lastApplied, nextIndex, matchIndex, votes, electionTimeout, heartbeatTimeout, messages, msgId, snapshotIndex, snapshotTerm, snapshotInProgress, nodeConfig>>

ApplyConfigChange(n, index) ==
    /\ index <= commitIndex[n]
    /\ index > lastApplied[n]
    /\ index <= Len(log[n])
    /\ log[n][index].type \in {"AddNode", "RemoveNode", "AddNonVotingNode"}
    /\ lastApplied' = [lastApplied EXCEPT ![n] = index]
    /\ IF log[n][index].type = "AddNode"
       THEN nodeConfig' = [nodeConfig EXCEPT ![log[n][index].data] = [voting |-> TRUE, active |-> TRUE]]
       ELSE IF log[n][index].type = "RemoveNode"
       THEN nodeConfig' = [nodeConfig EXCEPT ![log[n][index].data] = [voting |-> FALSE, active |-> FALSE]]
       ELSE UNCHANGED nodeConfig
    /\ configChangeInProgress' = [configChangeInProgress EXCEPT ![n] = FALSE]
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, votes, electionTimeout, heartbeatTimeout, messages, msgId, snapshotIndex, snapshotTerm, snapshotInProgress>>

SnapshotBegin(n) ==
    /\ ~snapshotInProgress[n]
    /\ commitIndex[n] > snapshotIndex[n]
    /\ snapshotInProgress' = [snapshotInProgress EXCEPT ![n] = TRUE]
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, votes, electionTimeout, heartbeatTimeout, messages, msgId, snapshotIndex, snapshotTerm, nodeConfig, configChangeInProgress>>

SnapshotEnd(n) ==
    /\ snapshotInProgress[n]
    /\ snapshotIndex' = [snapshotIndex EXCEPT ![n] = commitIndex[n]]
    /\ snapshotTerm' = [snapshotTerm EXCEPT ![n] = IF commitIndex[n] > 0 /\ commitIndex[n] <= Len(log[n]) THEN log[n][commitIndex[n]].term ELSE 0]
    /\ snapshotInProgress' = [snapshotInProgress EXCEPT ![n] = FALSE]
    /\ log' = [log EXCEPT ![n] = SubSeq(log[n], commitIndex[n] + 1, Len(log[n]))]
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, lastApplied, nextIndex, matchIndex, votes, electionTimeout, heartbeatTimeout, messages, msgId, nodeConfig, configChangeInProgress>>

Next ==
    \/ \E n \in Nodes : 
        \/ BecomeFollower(n)
        \/ BecomePreCandidate(n)
        \/ BecomeCandidate(n)
        \/ BecomeLeader(n)
        \/ ElectionStart(n)
        \/ PeriodicElectionTimeout(n)
        \/ PeriodicHeartbeat(n)
        \/ RecvRequestVote(n)
        \/ RecvRequestVoteResponse(n)
        \/ RecvAppendEntries(n)
        \/ RecvAppendEntriesResponse(n)
        \/ LogCommit(n)
        \/ SnapshotBegin(n)
        \/ SnapshotEnd(n)
        \/ \E m \in Nodes : SendRequestVote(n, m)
        \/ \E m \in Nodes : SendAppendEntries(n, m)
        \/ \E entry \in [type: LogEntryTypes, data: Nodes \cup {""}] : LogAppend(n, entry)
        \/ \E index \in 1..MaxLogLen : LogDelete(n, index)
        \/ \E newNode \in Nodes : AddNode(n, newNode)
        \/ \E oldNode \in Nodes : RemoveNode(n, oldNode)
        \/ \E index \in 1..MaxLogLen : ApplyConfigChange(n, index)

Spec == Init /\ [][Next]_vars

====