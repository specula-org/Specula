---- MODULE etcdraft ----
EXTENDS Naturals, Sequences, FiniteSets, TLC
CONSTANTS Node, Key, Value, Client, NULL

VARIABLES 
  state, currentTerm, votedFor, log, commitIndex, lastApplied,
  nextIndex, matchIndex, leaderId, store, messages,
  clientRequests, clientResponses, pendingReadIndexMessages,
  uncommittedSize, maxUncommittedSize, electionTimeout,
  randomizedElectionTimeout, electionElapsed, heartbeatElapsed

vars == <<state, currentTerm, votedFor, log, commitIndex, lastApplied,
          nextIndex, matchIndex, leaderId, store, messages,
          clientRequests, clientResponses, pendingReadIndexMessages,
          uncommittedSize, maxUncommittedSize, electionTimeout,
          randomizedElectionTimeout, electionElapsed, heartbeatElapsed>>

StateType == {"Follower", "Candidate", "Leader"}
MessageType == {"MsgHup", "MsgBeat", "MsgProp", "MsgApp", "MsgAppResp",
                "MsgVote", "MsgVoteResp", "MsgSnap", "MsgHeartbeat",
                "MsgHeartbeatResp", "MsgReadIndex", "MsgReadIndexResp"}

Entry == [term : Nat, type : {"Normal", "ConfChange", "ConfChangeV2"}, 
          data : [op: {"PUT", "GET", "DEL"}, key: Key, value: Value, client: Client]]

Log == [entries : Seq(Entry), committed : Nat, applied : Nat]

Message == [type : MessageType, from : Node, to : Node, term : Nat,
            index : Nat, logTerm : Nat, entries : Seq(Entry), 
            commit : Nat, reject : BOOLEAN, rejectHint : Nat,
            snapshot : [data : Seq(Entry), metadata : [index : Nat, term : Nat]]]

ClientRequest == [client : Client, op : {"PUT", "GET", "DEL"}, key : Key, value : Value]
ClientResponse == [client : Client, success : BOOLEAN, value : Value]

Min(a,b) == IF a <= b THEN a ELSE b

Init == 
    /\ state = [n \in Node |-> "Follower"]
    /\ currentTerm = [n \in Node |-> 0]
    /\ votedFor = [n \in Node |-> NULL]
    /\ log = [n \in Node |-> [entries |-> <<>>, committed |-> 0, applied |-> 0]]
    /\ commitIndex = [n \in Node |-> 0]
    /\ lastApplied = [n \in Node |-> 0]
    /\ nextIndex = [n \in Node |-> [m \in Node |-> 1]]
    /\ matchIndex = [n \in Node |-> [m \in Node |-> 0]]
    /\ leaderId = [n \in Node |-> NULL]
    /\ store = [n \in Node |-> [k \in Key |-> NULL]]
    /\ messages = {}
    /\ clientRequests = {}
    /\ clientResponses = {}
    /\ pendingReadIndexMessages = {}
    /\ uncommittedSize = [n \in Node |-> 0]
    /\ maxUncommittedSize = [n \in Node |-> 10]
    /\ electionTimeout = [n \in Node |-> 10]
    /\ randomizedElectionTimeout = [n \in Node |-> 15]
    /\ electionElapsed = [n \in Node |-> 0]
    /\ heartbeatElapsed = [n \in Node |-> 0]

TermAt(log, index) == 
    IF index > 0 /\ index <= Len(log.entries) THEN log.entries[index].term
    ELSE 0

LastEntry(log) == 
    LET len == Len(log.entries) IN
    IF len > 0 THEN [index |-> len, term |-> log.entries[len].term]
    ELSE [index |-> 0, term |-> 0]

AppendEntries(log, prevIndex, prevTerm, newEntries) ==
    IF prevIndex > Len(log.entries) \/ (prevIndex > 0 /\ TermAt(log, prevIndex) # prevTerm)
    THEN FALSE
    ELSE [log EXCEPT !.entries = SubSeq(log.entries, 1, prevIndex) \o newEntries]

ApplyEntry(store, entry) ==
    IF entry.type = "Normal" THEN
        CASE entry.data.op = "PUT" -> [store EXCEPT ![entry.data.key] = entry.data.value]
        [] entry.data.op = "DEL" -> [store EXCEPT ![entry.data.key] = NULL]
        [] OTHER -> store
    ELSE store

Quorum(nodes) == Cardinality(nodes) \div 2 + 1

CanVote(self, candidate, lastLog, candidateLog) ==
    \/ votedFor[self] = candidate
    \/ (votedFor[self] = NULL /\ leaderId[self] = NULL)
    \/ (candidateLog.term > lastLog.term) 
    \/ (candidateLog.term = lastLog.term /\ candidateLog.index >= lastLog.index)

BecomeFollower(node, term, leader) ==
    /\ state' = [state EXCEPT ![node] = "Follower"]
    /\ currentTerm' = [currentTerm EXCEPT ![node] = term]
    /\ votedFor' = [votedFor EXCEPT ![node] = NULL]
    /\ leaderId' = [leaderId EXCEPT ![node] = leader]
    /\ electionElapsed' = [electionElapsed EXCEPT ![node] = 0]
    /\ randomizedElectionTimeout' = [randomizedElectionTimeout EXCEPT ![node] = electionTimeout[node] + 1]

BecomeCandidate(node) ==
    /\ state' = [state EXCEPT ![node] = "Candidate"]
    /\ currentTerm' = [currentTerm EXCEPT ![node] = currentTerm[node] + 1]
    /\ votedFor' = [votedFor EXCEPT ![node] = node]
    /\ leaderId' = [leaderId EXCEPT ![node] = NULL]
    /\ electionElapsed' = [electionElapsed EXCEPT ![node] = 0]
    /\ randomizedElectionTimeout' = [randomizedElectionTimeout EXCEPT ![node] = electionTimeout[node] + 1]

BecomeLeader(node) ==
    /\ state' = [state EXCEPT ![node] = "Leader"]
    /\ leaderId' = [leaderId EXCEPT ![node] = node]
    /\ nextIndex' = [nextIndex EXCEPT ![node] = [n \in Node |-> Len(log[node].entries) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![node] = [n \in Node |-> 0]]
    /\ LET emptyEntry == [term |-> currentTerm[node], type |-> "Normal", data |-> NULL] IN
        log' = [log EXCEPT ![node] = [entries |-> log[node].entries \o <<emptyEntry>>, 
                                      committed |-> log[node].committed,
                                      applied |-> log[node].applied]]

SendMessage(msg) ==
    messages' = messages \cup {msg}

HandleAppendEntries(node, msg) ==
    LET selfLog == log[node] IN
    IF msg.term < currentTerm[node] THEN
        SendMessage([type |-> "MsgAppResp", from |-> node, to |-> msg.from, 
                     term |-> currentTerm[node], index |-> msg.index, reject |-> TRUE,
                     rejectHint |-> Len(selfLog.entries)])
    ELSE
        LET newTerm == IF msg.term > currentTerm[node] THEN msg.term ELSE currentTerm[node] IN
        /\ \/ /\ msg.term > currentTerm[node]
              /\ state' = [state EXCEPT ![node] = "Follower"]
              /\ currentTerm' = [currentTerm EXCEPT ![node] = newTerm]
              /\ votedFor' = [votedFor EXCEPT ![node] = NULL]
              /\ leaderId' = [leaderId EXCEPT ![node] = msg.from]
              /\ electionElapsed' = [electionElapsed EXCEPT ![node] = 0]
              /\ randomizedElectionTimeout' = [randomizedElectionTimeout EXCEPT ![node] = electionTimeout[node] + 1]
           \/ /\ msg.term <= currentTerm[node]
              /\ UNCHANGED <<state, currentTerm, votedFor, leaderId, electionElapsed, randomizedElectionTimeout>>
        /\ LET newLog == AppendEntries(selfLog, msg.index, msg.logTerm, msg.entries) IN
            IF newLog # FALSE THEN
                /\ log' = [log EXCEPT ![node] = newLog]
                /\ commitIndex' = [commitIndex EXCEPT ![node] = Min(msg.commit, Len(newLog.entries))]
                /\ SendMessage([type |-> "MsgAppResp", from |-> node, to |-> msg.from, 
                                term |-> newTerm, index |-> Len(newLog.entries)])
            ELSE
                /\ SendMessage([type |-> "MsgAppResp", from |-> node, to |-> msg.from, 
                                term |-> newTerm, index |-> msg.index, reject |-> TRUE,
                                rejectHint |-> Len(selfLog.entries)])

HandleVoteRequest(node, msg) ==
    LET lastLog == LastEntry(log[node]) IN
    IF msg.term < currentTerm[node] THEN
        SendMessage([type |-> "MsgVoteResp", from |-> node, to |-> msg.from, 
                     term |-> currentTerm[node], reject |-> TRUE])
    ELSE
        /\ IF msg.term > currentTerm[node] THEN
               BecomeFollower(node, msg.term, NULL)
           ELSE
               UNCHANGED <<state, currentTerm, votedFor, leaderId, electionElapsed, randomizedElectionTimeout>>
        /\ IF CanVote(node, msg.from, lastLog, [index |-> msg.index, term |-> msg.logTerm]) THEN
               /\ votedFor' = [votedFor EXCEPT ![node] = msg.from]
               /\ SendMessage([type |-> "MsgVoteResp", from |-> node, to |-> msg.from, 
                               term |-> currentTerm[node]])
           ELSE
               /\ SendMessage([type |-> "MsgVoteResp", from |-> node, to |-> msg.from, 
                               term |-> currentTerm[node], reject |-> TRUE])

HandleClientRequest(node, msg) ==
    IF state[node] = "Leader" THEN
        LET newEntry == [term |-> currentTerm[node], type |-> "Normal", 
                         data |-> [op |-> msg.op, key |-> msg.key, value |-> msg.value, client |-> msg.client]] IN
        /\ log' = [log EXCEPT ![node] = [entries |-> log[node].entries \o <<newEntry>>, 
                                         committed |-> log[node].committed,
                                         applied |-> log[node].applied]]
        /\ \E n \in Node \ {node} : 
                SendMessage([type |-> "MsgApp", from |-> node, to |-> n, term |-> currentTerm[node],
                             index |-> Len(log[node].entries), logTerm |-> TermAt(log[node], Len(log[node].entries)),
                             entries |-> <<newEntry>>, commit |-> log[node].committed])
        /\ uncommittedSize' = [uncommittedSize EXCEPT ![node] = uncommittedSize[node] + 1]
    ELSE
        /\ IF leaderId[node] # NULL THEN
               SendMessage([type |-> "ClientRequest", from |-> node, to |-> leaderId[node], 
                            op |-> msg.op, key |-> msg.key, value |-> msg.value, client |-> msg.client])

ApplyCommitted(node) ==
    LET selfLog == log[node] IN
    LET idx == selfLog.applied + 1 IN
    LET newStore == ApplyEntry(store[node], selfLog.entries[idx]) IN
    /\ idx <= selfLog.committed
    /\ store' = [store EXCEPT ![node] = newStore]
    /\ log' = [log EXCEPT ![node].applied = idx]
    /\ IF selfLog.entries[idx].type = "Normal" THEN
           clientResponses' = clientResponses \cup 
               { [client |-> selfLog.entries[idx].data.client, 
                 success |-> TRUE, 
                 value |-> newStore[selfLog.entries[idx].data.key]] }
       ELSE
           clientResponses' = clientResponses

AdvanceCommitIndex(node) ==
    LET selfLog == log[node] IN
    LET newCommit == 
        LET indices == { matchIndex[node][n] : n \in Node } IN
        LET maxIndex == Max(indices) IN
        LET quorumIndices == { i \in 1..maxIndex : 
                               Cardinality({ n \in Node : matchIndex[node][n] >= i }) >= Quorum(Node) } IN
        IF quorumIndices # {} THEN Max(quorumIndices) ELSE selfLog.committed
    IN
    /\ newCommit > selfLog.committed
    /\ newCommit <= Len(selfLog.entries)
    /\ TermAt(selfLog, newCommit) = currentTerm[node]
    /\ log' = [log EXCEPT ![node].committed = newCommit]
    /\ UNCHANGED <<store, clientResponses>>

Next ==
    \/ \E msg \in messages : 
        \E node \in Node :
            IF msg.to = node THEN
                \/ /\ msg.type = "MsgApp"
                   /\ HandleAppendEntries(node, msg)
                \/ /\ msg.type = "MsgVote"
                   /\ HandleVoteRequest(node, msg)
                \/ /\ msg.type = "ClientRequest"
                   /\ HandleClientRequest(node, msg)
    \/ \E node \in Node :
        \/ /\ state[node] \in {"Follower", "Candidate"}
           /\ electionElapsed[node] >= randomizedElectionTimeout[node]
           /\ BecomeCandidate(node)
        \/ /\ state[node] = "Leader"
           /\ heartbeatElapsed[node] >= electionTimeout[node]
           /\ \E n \in Node \ {node} : 
                  SendMessage([type |-> "MsgHeartbeat", from |-> node, to |-> n, 
                               term |-> currentTerm[node], commit |-> log[node].committed])
           /\ heartbeatElapsed' = [heartbeatElapsed EXCEPT ![node] = 0]
        \/ /\ state[node] = "Leader"
           /\ AdvanceCommitIndex(node)
        \/ /\ log[node].applied < log[node].committed
           /\ ApplyCommitted(node)
    \/ \E node \in Node :
        /\ electionElapsed' = [electionElapsed EXCEPT ![node] = electionElapsed[node] + 1]
        /\ heartbeatElapsed' = [heartbeatElapsed EXCEPT ![node] = heartbeatElapsed[node] + 1]
        /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars
====