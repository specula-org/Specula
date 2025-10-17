---- MODULE redisraft ----
EXTENDS TLC, Sequences, Naturals, FiniteSets
CONSTANTS Nodes, None, ElectionTimeoutRange
VARIABLES clusterNodes, term, votedFor, state, leaderId, commitIndex, lastApplied, log, nextIndex, matchIndex, votesReceived, electionTimeout, timeElapsed, messages
Message == [type: {"RequestVote", "RequestVoteResponse", "AppendEntries", "AppendEntriesResponse"}, sender: Nodes, receiver: Nodes, term: Nat, candidateId: Nodes, lastLogIndex: Nat, lastLogTerm: Nat, prevote: BOOLEAN, voteGranted: BOOLEAN, requestTerm: Nat, leaderId: Nodes, prevLogIndex: Nat, prevLogTerm: Nat, entries: Seq(Nat), leaderCommit: Nat, success: BOOLEAN, currentIdx: Nat]
Init == 
    clusterNodes \subseteq Nodes /\ clusterNodes # {} 
    /\ term = [node \in Nodes |-> 0] 
    /\ votedFor = [node \in Nodes |-> None] 
    /\ state = [node \in Nodes |-> "Follower"] 
    /\ leaderId = [node \in Nodes |-> None] 
    /\ commitIndex = [node \in Nodes |-> 0] 
    /\ lastApplied = [node \in Nodes |-> 0] 
    /\ log = [node \in Nodes |-> << >>] 
    /\ nextIndex = [node \in Nodes |-> [other \in Nodes |-> 1]] 
    /\ matchIndex = [node \in Nodes |-> [other \in Nodes |-> 0]] 
    /\ votesReceived = [node \in Nodes |-> {}] 
    /\ electionTimeout = [node \in Nodes |-> CHOOSE t \in ElectionTimeoutRange : TRUE] 
    /\ timeElapsed = [node \in Nodes |-> 0] 
    /\ messages = {}
vars == << clusterNodes, term, votedFor, state, leaderId, commitIndex, lastApplied, log, nextIndex, matchIndex, votesReceived, electionTimeout, timeElapsed, messages >>
AdvanceTime == 
    /\ \A node \in clusterNodes : timeElapsed'[node] = timeElapsed[node] + 1 
    /\ UNCHANGED << clusterNodes, term, votedFor, state, leaderId, commitIndex, lastApplied, log, nextIndex, matchIndex, votesReceived, electionTimeout, messages >>
ElectionTimeout(node) == 
    /\ node \in clusterNodes 
    /\ state[node] = "Follower" 
    /\ timeElapsed[node] >= electionTimeout[node] 
    /\ state' = [state EXCEPT ![node] = "PreCandidate"] 
    /\ timeElapsed' = [timeElapsed EXCEPT ![node] = 0] 
    /\ electionTimeout' = [electionTimeout EXCEPT ![node] = CHOOSE newTimeout \in ElectionTimeoutRange : TRUE] 
    /\ votesReceived' = [votesReceived EXCEPT ![node] = {}] 
    /\ LET currentIndex == Len(log[node]) IN
       LET lastLogTerm == IF currentIndex = 0 THEN 0 ELSE log[node][currentIndex] IN 
       messages' = messages \cup { [type |-> "RequestVote", sender |-> node, receiver |-> other, term |-> term[node] + 1, candidateId |-> node, lastLogIndex |-> currentIndex, lastLogTerm |-> lastLogTerm, prevote |-> TRUE] : other \in clusterNodes \ {node} } 
    /\ UNCHANGED << clusterNodes, term, votedFor, leaderId, commitIndex, lastApplied, log, nextIndex, matchIndex >>
RecvRequestVote(msg) == 
    /\ msg \in messages 
    /\ msg["type"] = "RequestVote" 
    /\ msg["receiver"] \in clusterNodes 
    /\ LET node == msg["receiver"] IN
       LET sender == msg["sender"] IN
       LET currentIndex == Len(log[node]) IN
       LET lastLogTerm == IF currentIndex = 0 THEN 0 ELSE log[node][currentIndex] IN 
       IF msg["term"] > term[node] THEN 
           /\ term' = [term EXCEPT ![node] = msg["term"]] 
           /\ votedFor' = [votedFor EXCEPT ![node] = None] 
           /\ state' = [state EXCEPT ![node] = "Follower"] 
           /\ leaderId' = [leaderId EXCEPT ![node] = None] 
           /\ timeElapsed' = [timeElapsed EXCEPT ![node] = 0] 
           /\ electionTimeout' = [electionTimeout EXCEPT ![node] = CHOOSE newTimeout \in ElectionTimeoutRange : TRUE] 
       ELSE 
           UNCHANGED << term, votedFor, state, leaderId, timeElapsed, electionTimeout >>
       /\ IF msg["term"] < term[node] THEN 
             messages' = messages \cup {[type |-> "RequestVoteResponse", sender |-> node, receiver |-> sender, term |-> term[node], voteGranted |-> FALSE, requestTerm |-> msg["term"], prevote |-> msg["prevote"]]} 
         ELSE 
             IF (votedFor[node] # None /\ votedFor[node] # msg["candidateId"]) \/ (msg["lastLogTerm"] < lastLogTerm \/ (msg["lastLogTerm"] = lastLogTerm /\ msg["lastLogIndex"] < currentIndex)) THEN 
                 messages' = messages \cup {[type |-> "RequestVoteResponse", sender |-> node, receiver |-> sender, term |-> term[node], voteGranted |-> FALSE, requestTerm |-> msg["term"], prevote |-> msg["prevote"]]} 
             ELSE 
                 /\ messages' = messages \cup {[type |-> "RequestVoteResponse", sender |-> node, receiver |-> sender, term |-> term[node], voteGranted |-> TRUE, requestTerm |-> msg["term"], prevote |-> msg["prevote"]]} 
                 /\ IF ~ msg["prevote"] THEN 
                        /\ votedFor' = [votedFor EXCEPT ![node] = msg["candidateId"]] 
                        /\ leaderId' = [leaderId EXCEPT ![node] = None] 
                        /\ timeElapsed' = [timeElapsed EXCEPT ![node] = 0] 
                    ELSE 
                        UNCHANGED << votedFor, leaderId, timeElapsed >> 
       /\ messages' = messages \ {msg} 
       /\ UNCHANGED << clusterNodes, commitIndex, lastApplied, log, nextIndex, matchIndex, votesReceived >>
RecvRequestVoteResponse(msg) == 
    /\ msg \in messages 
    /\ msg["type"] = "RequestVoteResponse" 
    /\ msg["receiver"] \in clusterNodes 
    /\ LET node == msg["receiver"] IN
       LET sender == msg["sender"] IN
       IF msg["term"] > term[node] THEN 
           /\ term' = [term EXCEPT ![node] = msg["term"]] 
           /\ votedFor' = [votedFor EXCEPT ![node] = None] 
           /\ state' = [state EXCEPT ![node] = "Follower"] 
           /\ leaderId' = [leaderId EXCEPT ![node] = None] 
           /\ timeElapsed' = [timeElapsed EXCEPT ![node] = 0] 
           /\ electionTimeout' = [electionTimeout EXCEPT ![node] = CHOOSE newTimeout \in ElectionTimeoutRange : TRUE] 
           /\ votesReceived' = [votesReceived EXCEPT ![node] = {}] 
       ELSE 
           UNCHANGED << term, votedFor, state, leaderId, timeElapsed, electionTimeout, votesReceived >> 
       /\ IF (state[node] = "PreCandidate" /\ msg["prevote"] /\ msg["requestTerm"] = term[node] + 1) \/ (state[node] = "Candidate" /\ ~ msg["prevote"] /\ msg["requestTerm"] = term[node]) THEN 
             IF msg["voteGranted"] THEN 
                 /\ votesReceived' = [votesReceived EXCEPT ![node] = votesReceived[node] \cup {sender}] 
                 /\ LET numVotes == Cardinality(votesReceived[node] \cup {sender}) IN
                    LET numNodes == Cardinality(clusterNodes) IN
                    IF numVotes > numNodes \div 2 THEN 
                        IF state[node] = "PreCandidate" THEN 
                            /\ state' = [state EXCEPT ![node] = "Candidate"] 
                            /\ term' = [term EXCEPT ![node] = term[node] + 1] 
                            /\ votedFor' = [votedFor EXCEPT ![node] = node] 
                            /\ timeElapsed' = [timeElapsed EXCEPT ![node] = 0] 
                            /\ electionTimeout' = [electionTimeout EXCEPT ![node] = CHOOSE newTimeout \in ElectionTimeoutRange : TRUE] 
                            /\ votesReceived' = [votesReceived EXCEPT ![node] = {}] 
                            /\ LET currentIndex == Len(log[node]) IN
                               LET lastLogTerm == IF currentIndex = 0 THEN 0 ELSE log[node][currentIndex] IN 
                               messages' = messages \cup { [type |-> "RequestVote", sender |-> node, receiver |-> other, term |-> term[node], candidateId |-> node, lastLogIndex |-> currentIndex, lastLogTerm |-> lastLogTerm, prevote |-> FALSE] : other \in clusterNodes \ {node} } 
                        ELSE 
                            /\ state' = [state EXCEPT ![node] = "Leader"] 
                            /\ leaderId' = [leaderId EXCEPT ![node] = node] 
                            /\ nextIndex' = [nextIndex EXCEPT ![node] = [follower \in Nodes |-> Len(log[node]) + 1]] 
                            /\ matchIndex' = [matchIndex EXCEPT ![node] = [follower \in Nodes |-> 0]] 
                            /\ timeElapsed' = [timeElapsed EXCEPT ![node] = 0] 
                            /\ LET prevLogTerm == IF Len(log[node]) = 0 THEN 0 ELSE log[node][Len(log[node])] IN
                               messages' = messages \cup { [type |-> "AppendEntries", sender |-> node, receiver |-> other, term |-> term[node], leaderId |-> node, prevLogIndex |-> Len(log[node]), prevLogTerm |-> prevLogTerm, entries |-> << >>, leaderCommit |-> commitIndex[node]] : other \in clusterNodes \ {node} } 
                    ELSE 
                        UNCHANGED << state, term, votedFor, leaderId, nextIndex, matchIndex, timeElapsed, messages >> 
             ELSE 
                 UNCHANGED << votesReceived, messages >> 
         ELSE 
             UNCHANGED << votesReceived, messages >> 
       /\ messages' = messages \ {msg} 
       /\ UNCHANGED << clusterNodes, commitIndex, lastApplied, log >>
AddNode(newNode) == 
    /\ newNode \in Nodes \ clusterNodes 
    /\ clusterNodes' = clusterNodes \cup {newNode} 
    /\ term' = [term EXCEPT ![newNode] = 0] 
    /\ votedFor' = [votedFor EXCEPT ![newNode] = None] 
    /\ state' = [state EXCEPT ![newNode] = "Follower"] 
    /\ leaderId' = [leaderId EXCEPT ![newNode] = None] 
    /\ commitIndex' = [commitIndex EXCEPT ![newNode] = 0] 
    /\ lastApplied' = [lastApplied EXCEPT ![newNode] = 0] 
    /\ log' = [log EXCEPT ![newNode] = << >>] 
    /\ nextIndex' = [nextIndex EXCEPT ![newNode] = [other \in Nodes |-> 1]] 
    /\ matchIndex' = [matchIndex EXCEPT ![newNode] = [other \in Nodes |-> 0]] 
    /\ votesReceived' = [votesReceived EXCEPT ![newNode] = {}] 
    /\ electionTimeout' = [electionTimeout EXCEPT ![newNode] = CHOOSE t \in ElectionTimeoutRange : TRUE] 
    /\ timeElapsed' = [timeElapsed EXCEPT ![newNode] = 0] 
    /\ UNCHANGED messages
RemoveNode(nodeToRemove) == 
    /\ nodeToRemove \in clusterNodes 
    /\ clusterNodes' = clusterNodes \ {nodeToRemove} 
    /\ UNCHANGED << term, votedFor, state, leaderId, commitIndex, lastApplied, log, nextIndex, matchIndex, votesReceived, electionTimeout, timeElapsed, messages >>
RecvAppendEntries(msg) == 
    /\ msg \in messages 
    /\ msg["type"] = "AppendEntries" 
    /\ msg["receiver"] \in clusterNodes 
    /\ LET node == msg["receiver"] IN 
      IF msg["term"] > term[node] THEN 
          /\ term' = [term EXCEPT ![node] = msg["term"]] 
          /\ votedFor' = [votedFor EXCEPT ![node] = None] 
          /\ state' = [state EXCEPT ![node] = "Follower"] 
          /\ leaderId' = [leaderId EXCEPT ![node] = msg["leaderId"]] 
          /\ timeElapsed' = [timeElapsed EXCEPT ![node] = 0] 
          /\ electionTimeout' = [electionTimeout EXCEPT ![node] = CHOOSE newTimeout \in ElectionTimeoutRange : TRUE] 
      ELSE 
          UNCHANGED << term, votedFor, state, leaderId, timeElapsed, electionTimeout >> 
      /\ IF msg["term"] < term[node] THEN 
            messages' = messages \cup {[type |-> "AppendEntriesResponse", sender |-> node, receiver |-> msg["sender"], term |-> term[node], success |-> FALSE, currentIdx |-> Len(log[node])]} 
        ELSE 
            LET prevIndex == msg["prevLogIndex"] IN 
            LET prevTerm == IF prevIndex = 0 THEN 0 ELSE log[node][prevIndex] IN 
            IF prevIndex > Len(log[node]) \/ prevTerm # msg["prevLogTerm"] THEN 
                messages' = messages \cup {[type |-> "AppendEntriesResponse", sender |-> node, receiver |-> msg["sender"], term |-> term[node], success |-> FALSE, currentIdx |-> Len(log[node])]} 
            ELSE 
                /\ LET newLog == IF prevIndex = Len(log[node]) THEN log[node] \o msg["entries"] 
                                 ELSE SubSeq(log[node], 1, prevIndex) \o msg["entries"] 
                log' = [log EXCEPT ![node] = newLog] 
                /\ IF msg["leaderCommit"] > commitIndex[node] THEN 
                       commitIndex' = [commitIndex EXCEPT ![node] = Min(msg["leaderCommit"], Len(newLog))] 
                   ELSE 
                       UNCHANGED commitIndex 
                /\ messages' = messages \cup {[type |-> "AppendEntriesResponse", sender |-> node, receiver |-> msg["sender"], term |-> term[node], success |-> TRUE, currentIdx |-> Len(newLog)]} 
      /\ messages' = messages \ {msg} 
      /\ UNCHANGED << clusterNodes, votedFor, state, leaderId, timeElapsed, electionTimeout, nextIndex, matchIndex, votesReceived, lastApplied >>
RecvAppendEntriesResponse(msg) == 
    /\ msg \in messages 
    /\ msg["type"] = "AppendEntriesResponse" 
    /\ msg["receiver"] \in clusterNodes 
    /\ LET node == msg["receiver"] IN
       LET sender == msg["sender"] IN
       IF msg["term"] > term[node] THEN 
           /\ term' = [term EXCEPT ![node] = msg["term"]] 
           /\ votedFor' = [votedFor EXCEPT ![node] = None] 
           /\ state' = [state EXCEPT ![node] = "Follower"] 
           /\ leaderId' = [leaderId EXCEPT ![node] = None] 
           /\ timeElapsed' = [timeElapsed EXCEPT ![node] = 0] 
           /\ electionTimeout' = [electionTimeout EXCEPT ![node] = CHOOSE newTimeout \in ElectionTimeoutRange : TRUE] 
       ELSE 
           UNCHANGED << term, votedFor, state, leaderId, timeElapsed, electionTimeout >> 
       /\ IF state[node] = "Leader" THEN 
             IF msg["success"] THEN 
                 /\ matchIndex' = [matchIndex EXCEPT ![node][sender] = msg["currentIdx"]] 
                 /\ nextIndex' = [nextIndex EXCEPT ![node][sender] = msg["currentIdx"] + 1] 
                 /\ LET S == {i \in commitIndex[node] + 1 .. Len(log[node]) : 
                            Cardinality({other \in clusterNodes : matchIndex[node][other] >= i}) > Cardinality(clusterNodes) \div 2 
                            /\ log[node][i] = term[node] } 
                 IN 
                 IF S # {} THEN 
                    LET maxN == CHOOSE n \in S : \A m \in S : m <= n IN 
                    commitIndex' = [commitIndex EXCEPT ![node] = maxN] 
                 ELSE 
                    UNCHANGED commitIndex 
             ELSE 
                 nextIndex' = [nextIndex EXCEPT ![node][sender] = Max(1, nextIndex[node][sender] - 1)] 
         ELSE 
             UNCHANGED << nextIndex, matchIndex, commitIndex >> 
       /\ messages' = messages \ {msg} 
       /\ UNCHANGED << clusterNodes, log, votesReceived, lastApplied >>
SendHeartbeat(node) == 
    /\ node \in clusterNodes 
    /\ state[node] = "Leader" 
    /\ LET prevLogTerm == IF Len(log[node]) = 0 THEN 0 ELSE log[node][Len(log[node])] IN
       messages' = messages \cup { [type |-> "AppendEntries", sender |-> node, receiver |-> other, term |-> term[node], leaderId |-> node, prevLogIndex |-> Len(log[node]), prevLogTerm |-> prevLogTerm, entries |-> << >>, leaderCommit |-> commitIndex[node]] : other \in clusterNodes \ {node} } 
    /\ UNCHANGED << clusterNodes, term, votedFor, state, leaderId, commitIndex, lastApplied, log, nextIndex, matchIndex, votesReceived, electionTimeout, timeElapsed >>
LeaderAppendEntry(node) == 
    /\ node \in clusterNodes 
    /\ state[node] = "Leader" 
    /\ LET newEntry == term[node] IN 
        log' = [log EXCEPT ![node] = log[node] \o << newEntry >>] 
    /\ UNCHANGED << clusterNodes, term, votedFor, state, leaderId, commitIndex, lastApplied, nextIndex, matchIndex, votesReceived, electionTimeout, timeElapsed, messages >>
AdvanceLastApplied(node) == 
    /\ node \in clusterNodes 
    /\ lastApplied[node] < commitIndex[node] 
    /\ lastApplied' = [lastApplied EXCEPT ![node] = commitIndex[node]] 
    /\ UNCHANGED << clusterNodes, term, votedFor, state, leaderId, commitIndex, log, nextIndex, matchIndex, votesReceived, electionTimeout, timeElapsed, messages >>
Next == 
    \/ AdvanceTime
    \/ \E node \in clusterNodes : ElectionTimeout(node)
    \/ \E msg \in messages : RecvRequestVote(msg)
    \/ \E msg \in messages : RecvRequestVoteResponse(msg)
    \/ \E msg \in messages : RecvAppendEntries(msg)
    \/ \E msg \in messages : RecvAppendEntriesResponse(msg)
    \/ \E newNode \in Nodes \ clusterNodes : AddNode(newNode)
    \/ \E nodeToRemove \in clusterNodes : RemoveNode(nodeToRemove)
    \/ \E node \in clusterNodes : SendHeartbeat(node)
    \/ \E node \in clusterNodes : LeaderAppendEntry(node)
    \/ \E node \in clusterNodes : AdvanceLastApplied(node)
Spec == Init /\ [][Next]_vars
====