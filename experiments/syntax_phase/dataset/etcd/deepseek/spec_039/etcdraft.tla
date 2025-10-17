---- MODULE etcdraft ----
EXTENDS Naturals, Sequences, FiniteSets, TLC
CONSTANTS Nodes, Keys, Values, None, ElectionTimeout, HeartbeatTimeout, MaxUncommittedSize
VARIABLES 
  state,
  currentTerm,
  votedFor,
  log,
  commitIndex,
  lastApplied,
  leaderId,
  nextIndex,
  matchIndex,
  uncommittedSize,
  electionElapsed,
  heartbeatElapsed,
  randomizedElectionTimeout,
  pendingReadIndexMessages,
  msgs,
  kvStore

vars == <<state, currentTerm, votedFor, log, commitIndex, lastApplied, leaderId, 
          nextIndex, matchIndex, uncommittedSize, electionElapsed, 
          heartbeatElapsed, randomizedElectionTimeout, pendingReadIndexMessages,
          msgs, kvStore>>

NodeSet == Nodes \cup {None}
Term == Nat
Index == Nat
LogEntry == [term : Term, index : Index, type: {"Put", "Get", "Delete", "None"}, key: Keys, value: Values \cup {None}, clientId: Nat, requestId: Nat]
MessageType == {"MsgHup", "MsgVote", "MsgVoteResp", "MsgApp", "MsgAppResp", "MsgHeartbeat", "MsgHeartbeatResp", "MsgReadIndex", "MsgReadIndexResp", "ClientRequest", "ClientResponse"}
Message == [type: MessageType, from: NodeSet, to: NodeSet, term: Term, logTerm: Term, index: Index, entries: Seq(LogEntry), commit: Index, reject: BOOLEAN, context: SUBSET STRING]

StateType == {"Follower", "Candidate", "Leader", "PreCandidate"}

Init == 
  /\ state = [n \in Nodes |-> "Follower"]
  /\ currentTerm = [n \in Nodes |-> 0]
  /\ votedFor = [n \in Nodes |-> None]
  /\ log = [n \in Nodes |-> <<>>]
  /\ commitIndex = [n \in Nodes |-> 0]
  /\ lastApplied = [n \in Nodes |-> 0]
  /\ leaderId = [n \in Nodes |-> None]
  /\ nextIndex = [n \in Nodes |-> [m \in Nodes |-> 1]]
  /\ matchIndex = [n \in Nodes |-> [m \in Nodes |-> 0]]
  /\ uncommittedSize = [n \in Nodes |-> 0]
  /\ electionElapsed = [n \in Nodes |-> 0]
  /\ heartbeatElapsed = [n \in Nodes |-> 0]
  /\ randomizedElectionTimeout = [n \in Nodes |-> ElectionTimeout + CHOOSE i \in 0..ElectionTimeout-1 : TRUE]
  /\ pendingReadIndexMessages = [n \in Nodes |-> <<>>]
  /\ msgs = {}
  /\ kvStore = [n \in Nodes |-> [k \in Keys |-> None]]

GetLastLogTerm(n) ==
  IF Len(log[n]) > 0 THEN log[n][Len(log[n])].term ELSE 0

GetLastLogIndex(n) ==
  Len(log[n])

LogUpToDate(candidateTerm, candidateIndex, n) ==
  \/ candidateTerm > GetLastLogTerm(n)
  \/ (candidateTerm = GetLastLogTerm(n) /\ candidateIndex >= GetLastLogIndex(n))

SafeAppendEntries(prevLogIndex, prevLogTerm, entries, n) ==
  /\ prevLogIndex <= GetLastLogIndex(n)
  /\ (prevLogIndex = 0 \/ (prevLogIndex <= GetLastLogIndex(n) /\ log[n][prevLogIndex].term = prevLogTerm))
  /\ \/ entries = <<>>
     \/ \A i \in 1..Len(entries) :
          prevLogIndex + i > GetLastLogIndex(n) \/ log[n][prevLogIndex + i].term = entries[i].term

Majority(S) == Cardinality(S) > Cardinality(Nodes) \div 2

CanGrantVote(m, n) ==
  \/ votedFor[n] = None
  \/ votedFor[n] = m.from

HandleRequestVote(n, m) ==
  IF m.term < currentTerm[n] THEN
    /\ msgs' = msgs \cup [type |-> "MsgVoteResp", from |-> n, to |-> m.from, term |-> currentTerm[n], reject |-> TRUE]
  ELSE
    LET updateTerm ==
        IF m.term > currentTerm[n] THEN
          /\ currentTerm' = [currentTerm EXCEPT ![n] = m.term]
          /\ state' = [state EXCEPT ![n] = "Follower"]
          /\ votedFor' = [votedFor EXCEPT ![n] = None]
        ELSE TRUE
    IN
    IF CanGrantVote(m, n) /\ LogUpToDate(m.term, m.index, n) THEN
      /\ updateTerm
      /\ votedFor' = [votedFor EXCEPT ![n] = m.from]
      /\ electionElapsed' = [electionElapsed EXCEPT ![n] = 0]
      /\ msgs' = msgs \cup [type |-> "MsgVoteResp", from |-> n, to |-> m.from, term |-> currentTerm'[n], reject |-> FALSE]
    ELSE
      /\ updateTerm
      /\ msgs' = msgs \cup [type |-> "MsgVoteResp", from |-> n, to |-> m.from, term |-> currentTerm'[n], reject |-> TRUE]

HandleAppendEntries(n, m) ==
  IF m.term < currentTerm[n] THEN
    /\ msgs' = msgs \cup [type |-> "MsgAppResp", from |-> n, to |-> m.from, term |-> currentTerm[n], index |-> m.index, reject |-> TRUE]
  ELSE
    LET becomeFollower ==
        /\ state' = [state EXCEPT ![n] = "Follower"]
        /\ leaderId' = [leaderId EXCEPT ![n] = m.from]
        /\ currentTerm' = [currentTerm EXCEPT ![n] = m.term]
        /\ electionElapsed' = [electionElapsed EXCEPT ![n] = 0]
    IN
    IF SafeAppendEntries(m.index, m.logTerm, m.entries, n) THEN
      LET
        L == Min({Len(m.entries), GetLastLogIndex(n) - m.index})
        conflictSet == {i \in 1..L : log[n][m.index + i].term # m.entries[i].term}
        conflictIndex == IF L = 0 THEN 0
                        ELSE IF conflictSet = {} THEN 0 ELSE Min(conflictSet)
        newEntries == IF conflictIndex > 0 THEN SubSeq(m.entries, conflictIndex, Len(m.entries)) ELSE m.entries
        newLog == IF m.index + Len(newEntries) > GetLastLogIndex(n) THEN
                    log[n] \o newEntries
                 ELSE
                    SubSeq(log[n], 1, m.index) \o newEntries
      IN
      /\ becomeFollower
      /\ log' = [log EXCEPT ![n] = newLog]
      /\ commitIndex' = [commitIndex EXCEPT ![n] = Min(m.commit, GetLastLogIndex(n))]
      /\ msgs' = msgs \cup [type |-> "MsgAppResp", from |-> n, to |-> m.from, term |-> currentTerm'[n], index |-> GetLastLogIndex(n), reject |-> FALSE]
    ELSE
      /\ becomeFollower
      /\ msgs' = msgs \cup [type |-> "MsgAppResp", from |-> n, to |-> m.from, term |-> currentTerm'[n], index |-> m.index, reject |-> TRUE]

HandleClientRequest(n, m) ==
  LET
    entry == [term |-> currentTerm[n], index |-> GetLastLogIndex(n) + 1, type |-> m.op.type, key |-> m.op.key, value |-> m.op.value, clientId |-> m.clientId, requestId |-> m.requestId]
    newSize == IF m.op.type = "Put" THEN 1 ELSE 0
  IN
  IF state[n] = "Leader" /\ uncommittedSize[n] + newSize <= MaxUncommittedSize THEN
    /\ log' = [log EXCEPT ![n] = Append(log[n], entry)]
    /\ uncommittedSize' = [uncommittedSize EXCEPT ![n] = uncommittedSize[n] + newSize]
    /\ nextIndex' = [nextIndex EXCEPT ![n][n] = GetLastLogIndex(n) + 1]
    /\ matchIndex' = [matchIndex EXCEPT ![n][n] = GetLastLogIndex(n)]
    /\ msgs' = msgs \cup [type |-> "MsgApp", from |-> n, to |-> n, term |-> currentTerm[n], index |-> GetLastLogIndex(n), logTerm |-> GetLastLogTerm(n), entries |-> <<entry>>, commit |-> commitIndex[n]]

ApplyLogEntry(n, entry) ==
  /\ IF entry.type = "Put" THEN
        kvStore' = [kvStore EXCEPT ![n][entry.key] = entry.value]
     ELSE IF entry.type = "Delete" THEN
        kvStore' = [kvStore EXCEPT ![n][entry.key] = None]
     ELSE TRUE
  /\ msgs' = msgs \cup [type |-> "ClientResponse", from |-> n, to |-> None, clientId |-> entry.clientId, requestId |-> entry.requestId, result |-> kvStore[n][entry.key]]
  /\ lastApplied' = [lastApplied EXCEPT ![n] = entry.index]

BecomeLeader(n) ==
  /\ state' = [state EXCEPT ![n] = "Leader"]
  /\ leaderId' = [leaderId EXCEPT ![n] = n]
  /\ nextIndex' = [nextIndex EXCEPT ![n] = [m \in Nodes |-> GetLastLogIndex(n) + 1]]
  /\ matchIndex' = [matchIndex EXCEPT ![n] = [m \in Nodes |-> 0]]
  /\ LET emptyEntry == [term |-> currentTerm[n], index |-> GetLastLogIndex(n) + 1, type |-> "None", key |-> None, value |-> None, clientId |-> 0, requestId |-> 0]
     IN
     /\ log' = [log EXCEPT ![n] = Append(log[n], emptyEntry)]
     /\ msgs' = msgs \cup [type |-> "MsgApp", from |-> n, to |-> n, term |-> currentTerm[n], index |-> GetLastLogIndex(n), logTerm |-> GetLastLogTerm(n), entries |-> <<emptyEntry>>, commit |-> commitIndex[n]]

AdvanceCommitIndex(n) ==
  LET
    S == {k \in 1..GetLastLogIndex(n) : 
            log[n][k].term = currentTerm[n] /\
            Cardinality({m \in Nodes : matchIndex[n][m] >= k}) > Cardinality(Nodes) \div 2}
    maxS == IF S = {} THEN 0 ELSE CHOOSE x \in S : \A y \in S : y <= x
  IN
  IF maxS > commitIndex[n] THEN
    /\ commitIndex' = [commitIndex EXCEPT ![n] = maxS]

Next ==
  \/ \E n \in Nodes : 
        /\ electionElapsed[n] >= randomizedElectionTimeout[n]
        /\ state[n] \in {"Follower", "Candidate"}
        /\ state' = [state EXCEPT ![n] = "Candidate"]
        /\ currentTerm' = [currentTerm EXCEPT ![n] = currentTerm[n] + 1]
        /\ votedFor' = [votedFor EXCEPT ![n] = n]
        /\ electionElapsed' = [electionElapsed EXCEPT ![n] = 0]
        /\ randomizedElectionTimeout' = [randomizedElectionTimeout EXCEPT ![n] = ElectionTimeout + CHOOSE i \in 0..ElectionTimeout-1 : TRUE]
        /\ msgs' = msgs \cup [type |-> "MsgVote", from |-> n, to |-> Nodes \ {n}, term |-> currentTerm'[n], index |-> GetLastLogIndex(n), logTerm |-> GetLastLogTerm(n)]
  \/ \E n \in Nodes, m \in msgs : 
        \/ /\ m.type = "MsgVote"
           /\ HandleRequestVote(n, m)
        \/ /\ m.type = "MsgVoteResp"
           /\ m.term = currentTerm[n]
           /\ state[n] \in {"Candidate", "PreCandidate"}
           /\ LET votes == {v \in Nodes : \E msg \in msgs : msg.type = "MsgVoteResp" /\ msg.from = v /\ msg.to = n /\ msg.term = currentTerm[n] /\ ~msg.reject}
              IN
              IF Cardinality(votes) > Cardinality(Nodes) \div 2 THEN
                BecomeLeader(n)
              ELSE
                UNCHANGED <<state, leaderId, nextIndex, matchIndex, log>>
        \/ /\ m.type = "MsgApp"
           /\ HandleAppendEntries(n, m)
        \/ /\ m.type = "MsgAppResp"
           /\ state[n] = "Leader"
           /\ m.term = currentTerm[n]
           /\ IF m.reject THEN
                /\ nextIndex' = [nextIndex EXCEPT ![n][m.from] = Max(1, nextIndex[n][m.from] - 1)]
              ELSE
                /\ nextIndex' = [nextIndex EXCEPT ![n][m.from] = m.index + 1]
                /\ matchIndex' = [matchIndex EXCEPT ![n][m.from] = m.index]
                /\ AdvanceCommitIndex(n)
        \/ /\ m.type = "ClientRequest"
           /\ HandleClientRequest(n, m)
  \/ \E n \in Nodes : 
        /\ state[n] = "Leader"
        /\ heartbeatElapsed[n] >= HeartbeatTimeout
        /\ heartbeatElapsed' = [heartbeatElapsed EXCEPT ![n] = 0]
        /\ msgs' = msgs \cup [type |-> "MsgHeartbeat", from |-> n, to |-> Nodes \ {n}, term |-> currentTerm[n], commit |-> commitIndex[n]]
  \/ \E n \in Nodes : 
        /\ lastApplied[n] < commitIndex[n]
        /\ LET i == lastApplied[n] + 1 IN
           LET entry == log[n][i] IN
               ApplyLogEntry(n, entry)
  \/ \E n \in Nodes : 
        /\ electionElapsed' = [electionElapsed EXCEPT ![n] = electionElapsed[n] + 1]
        /\ heartbeatElapsed' = [heartbeatElapsed EXCEPT ![n] = heartbeatElapsed[n] + 1]

TypeInvariant == 
  /\ state \in [Nodes -> StateType]
  /\ currentTerm \in [Nodes -> Nat]
  /\ votedFor \in [Nodes -> NodeSet]
  /\ log \in [Nodes -> Seq(LogEntry)]
  /\ commitIndex \in [Nodes -> Nat]
  /\ lastApplied \in [Nodes -> Nat]
  /\ leaderId \in [Nodes -> NodeSet]
  /\ nextIndex \in [Nodes -> [Nodes -> Nat]]
  /\ matchIndex \in [Nodes -> [Nodes -> Nat]]
  /\ uncommittedSize \in [Nodes -> Nat]
  /\ electionElapsed \in [Nodes -> Nat]
  /\ heartbeatElapsed \in [Nodes -> Nat]
  /\ randomizedElectionTimeout \in [Nodes -> Nat]
  /\ pendingReadIndexMessages \in [Nodes -> Seq(Message)]
  /\ msgs \subseteq Message
  /\ kvStore \in [Nodes -> [Keys -> Values \cup {None}]]

Consistency == 
  \A n1, n2 \in Nodes, i \in 1..Min(lastApplied[n1], lastApplied[n2]) : 
    log[n1][i] = log[n2][i]

Termination == 
  \A t \in Term : 
    Cardinality({n \in Nodes : currentTerm[n] = t /\ state[n] = "Leader"}) =< 1

Invariants == 
  /\ TypeInvariant
  /\ Consistency
  /\ Termination

====