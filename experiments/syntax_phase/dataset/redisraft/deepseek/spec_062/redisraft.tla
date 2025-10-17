---- MODULE redisraft ----
EXTENDS TLC, Sequences, Naturals, FiniteSets
CONSTANTS Servers, None, LogEntry
VARIABLES state, currentTerm, votedFor, log, commitIndex, lastApplied, leader, nodes, electionTimeout, timeoutElapsed, messages
vars == <<state, currentTerm, votedFor, log, commitIndex, lastApplied, leader, nodes, electionTimeout, timeoutElapsed, messages>>
Init == 
  state = [s \in Servers |-> "Follower"] /\
  currentTerm = [s \in Servers |-> 0] /\
  votedFor = [s \in Servers |-> None] /\
  log = [s \in Servers |-> <<>>] /\
  commitIndex = [s \in Servers |-> 0] /\
  lastApplied = [s \in Servers |-> 0] /\
  leader = [s \in Servers |-> None] /\
  nodes = Servers /\
  electionTimeout \in [Servers -> {n \in Nat : n > 0}] /\
  timeoutElapsed = [s \in Servers |-> 0] /\
  messages = {}
Next == 
  \/ \E s \in Servers : ElectionTimeout(s)
  \/ \E s \in Servers : BecomeCandidate(s)
  \/ \E s \in Servers : BecomeLeader(s)
  \/ \E s \in Servers : BecomeFollower(s)
  \/ \E s \in Servers : SendHeartbeat(s)
  \/ \E s \in Servers, m \in messages : m["receiver"] = s /\ ReceiveMessage(s, m)
  \/ AdvanceTime
  \/ \E n \in Servers : AddNode(n)
  \/ \E n \in nodes : RemoveNode(n)
  \/ \E s \in Servers : SnapshotBegin(s)
  \/ \E s \in Servers : SnapshotEnd(s)
ElectionTimeout(s) == 
  state[s] = "Follower" /\
  timeoutElapsed[s] >= electionTimeout[s] /\
  state[s]' = "PreCandidate" /\
  leader[s]' = None /\
  timeoutElapsed[s]' = 0 /\
  electionTimeout[s]' \in {n \in Nat : n > 0} /\
  messages' = messages \cup { [type |-> "RequestVote", sender |-> s, receiver |-> r, term |-> currentTerm[s] + 1, candidateId |-> s, lastLogIndex |-> Len(log[s]), lastLogTerm |-> (IF Len(log[s]) > 0 THEN log[s][Len(log[s])]["term"] ELSE 0), prevote |-> TRUE ] : r \in {x \in nodes : x # s} } /\
  UNCHANGED <<currentTerm, votedFor, log, commitIndex, lastApplied, nodes>>
BecomeCandidate(s) == 
  (state[s] = "PreCandidate" \/ state[s] = "Follower") /\
  currentTerm[s]' = currentTerm[s] + 1 /\
  votedFor[s]' = s /\
  state[s]' = "Candidate" /\
  leader[s]' = None /\
  timeoutElapsed[s]' = 0 /\
  electionTimeout[s]' \in {n \in Nat : n > 0} /\
  messages' = messages \cup { [type |-> "RequestVote", sender |-> s, receiver |-> r, term |-> currentTerm[s]', candidateId |-> s, lastLogIndex |-> Len(log[s]), lastLogTerm |-> (IF Len(log[s]) > 0 THEN log[s][Len(log[s])]["term"] ELSE 0), prevote |-> FALSE ] : r \in {x \in nodes : x # s} } /\
  UNCHANGED <<log, commitIndex, lastApplied, nodes>>
BecomeLeader(s) == 
  state[s] = "Candidate" /\
  state[s]' = "Leader" /\
  leader[s]' = s /\
  timeoutElapsed[s]' = 0 /\
  UNCHANGED <<currentTerm, votedFor, log, commitIndex, lastApplied, electionTimeout, messages, nodes>>
BecomeFollower(s) == 
  state[s]' = "Follower" /\
  leader[s]' = None /\
  timeoutElapsed[s]' = 0 /\
  electionTimeout[s]' \in {n \in Nat : n > 0} /\
  UNCHANGED <<currentTerm, votedFor, log, commitIndex, lastApplied, messages, nodes>>
SendHeartbeat(s) == 
  state[s] = "Leader" /\
  messages' = messages \cup { [type |-> "AppendEntries", sender |-> s, receiver |-> r, term |-> currentTerm[s], leaderId |-> s, prevLogIndex |-> Len(log[r]), prevLogTerm |-> (IF Len(log[r]) > 0 THEN log[r][Len(log[r])]["term"] ELSE 0), entries |-> <<>>, leaderCommit |-> commitIndex[s] ] : r \in {x \in nodes : x # s} } /\
  UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, leader, electionTimeout, timeoutElapsed, nodes>>
ReceiveMessage(s, m) == 
  m \in messages /\
  m["receiver"] = s /\
  IF m["type"] = "RequestVote" THEN
    IF m["term"] < currentTerm[s] THEN
      messages' = messages \ {m} \cup { [type |-> "RequestVoteResponse", sender |-> s, receiver |-> m["sender"], term |-> currentTerm[s], requestTerm |-> m["term"], voteGranted |-> FALSE, prevote |-> m["prevote"]] } /\
      UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, leader, nodes, electionTimeout, timeoutElapsed>>
    ELSE
      IF m["term"] > currentTerm[s] THEN
        currentTerm[s]' = m["term"] /\
        votedFor[s]' = None /\
        state[s]' = "Follower" /\
        leader[s]' = None /\
        timeoutElapsed[s]' = 0 /\
        electionTimeout[s]' \in {n \in Nat : n > 0} /\
        messages' = messages \ {m} /\
        UNCHANGED <<log, commitIndex, lastApplied, nodes>>
      ELSE
        UNCHANGED <<currentTerm, votedFor, state, leader, timeoutElapsed, electionTimeout, log, commitIndex, lastApplied, nodes>> /\
        LET logOk == (m["lastLogTerm"] > (IF Len(log[s]) > 0 THEN log[s][Len(log[s])]["term"] ELSE 0) \/ (m["lastLogTerm"] = (IF Len(log[s]) > 0 THEN log[s][Len(log[s])]["term"] ELSE 0) /\ m["lastLogIndex"] >= Len(log[s]))) IN
        IF (votedFor[s] = None \/ votedFor[s] = m["candidateId"]) /\ logOk THEN
          IF m["prevote"] THEN
            messages' = messages \ {m} \cup { [type |-> "RequestVoteResponse", sender |-> s, receiver |-> m["sender"], term |-> currentTerm[s], requestTerm |-> m["term"], voteGranted |-> TRUE, prevote |-> m["prevote"]] } /\
            UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, leader, nodes, electionTimeout, timeoutElapsed>>
          ELSE
            votedFor[s]' = m["candidateId"] /\
            timeoutElapsed[s]' = 0 /\
            leader[s]' = None /\
            messages' = messages \ {m} \cup { [type |-> "RequestVoteResponse", sender |-> s, receiver |-> m["sender"], term |-> currentTerm[s], requestTerm |-> m["term"], voteGranted |-> TRUE, prevote |-> m["prevote"]] } /\
            UNCHANGED <<state, currentTerm, log, commitIndex, lastApplied, nodes, electionTimeout>>
        ELSE
          messages' = messages \ {m} \cup { [type |-> "RequestVoteResponse", sender |-> s, receiver |-> m["sender"], term |-> currentTerm[s], requestTerm |-> m["term"], voteGranted |-> FALSE, prevote |-> m["prevote"]] } /\
          UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, leader, nodes, electionTimeout, timeoutElapsed>>
  ELSE IF m["type"] = "RequestVoteResponse" THEN
    IF m["term"] > currentTerm[s] THEN
      currentTerm[s]' = m["term"] /\
      votedFor[s]' = None /\
      state[s]' = "Follower" /\
      leader[s]' = None /\
      timeoutElapsed[s]' = 0 /\
      electionTimeout[s]' \in {n \in Nat : n > 0} /\
      messages' = messages \ {m} /\
      UNCHANGED <<log, commitIndex, lastApplied, nodes>>
    ELSE
      IF (m["requestTerm"] = currentTerm[s] /\ \lnot m["prevote"]) \/ (m["prevote"] /\ m["requestTerm"] = currentTerm[s] + 1) THEN
        IF m["voteGranted"] THEN
          IF m["prevote"] THEN
            state[s]' = "Candidate" /\
            currentTerm[s]' = currentTerm[s] + 1 /\
            votedFor[s]' = s /\
            leader[s]' = None /\
            timeoutElapsed[s]' = 0 /\
            electionTimeout[s]' \in {n \in Nat : n > 0} /\
            messages' = messages \ {m} \cup { [type |-> "RequestVote", sender |-> s, receiver |-> r, term |-> currentTerm[s]', candidateId |-> s, lastLogIndex |-> Len(log[s]), lastLogTerm |-> (IF Len(log[s]) > 0 THEN log[s][Len(log[s])]["term"] ELSE 0), prevote |-> FALSE ] : r \in {x \in nodes : x # s} } /\
            UNCHANGED <<log, commitIndex, lastApplied>>
          ELSE
            state[s]' = "Leader" /\
            leader[s]' = s /\
            timeoutElapsed[s]' = 0 /\
            messages' = messages \ {m} /\
            UNCHANGED <<currentTerm, votedFor, log, commitIndex, lastApplied, electionTimeout>>
        ELSE
          messages' = messages \ {m} /\
          UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, leader, nodes, electionTimeout, timeoutElapsed>>
      ELSE
        messages' = messages \ {m} /\
        UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, leader, nodes, electionTimeout, timeoutElapsed>>
  ELSE IF m["type"] = "AppendEntries" THEN
    IF m["term"] < currentTerm[s] THEN
      messages' = messages \ {m} \cup { [type |-> "AppendEntriesResponse", sender |-> s, receiver |-> m["sender"], term |-> currentTerm[s], success |-> FALSE, currentIdx |-> Len(log[s]) ] } /\
      UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, leader, nodes, electionTimeout, timeoutElapsed>>
    ELSE
      IF m["term"] > currentTerm[s] THEN
        currentTerm[s]' = m["term"] /\
        votedFor[s]' = None /\
        state[s]' = "Follower" /\
        leader[s]' = m["leaderId"] /\
        timeoutElapsed[s]' = 0 /\
        electionTimeout[s]' \in {n \in Nat : n > 0} /\
        messages' = messages \ {m} /\
        UNCHANGED <<log, commitIndex, lastApplied, nodes>>
      ELSE
        UNCHANGED <<currentTerm, votedFor, state, leader, timeoutElapsed, electionTimeout, log, commitIndex, lastApplied, nodes>> /\
        IF m["prevLogIndex"] > Len(log[s]) \/ (m["prevLogIndex"] > 0 /\ log[s][m["prevLogIndex"]]["term"] # m["prevLogTerm"]) THEN
          messages' = messages \ {m} \cup { [type |-> "AppendEntriesResponse", sender |-> s, receiver |-> m["sender"], term |-> currentTerm[s], success |-> FALSE, currentIdx |-> Len(log[s]) ] } /\
          UNCHANGED <<state, currentTerm, votedFor, leader, nodes, electionTimeout, timeoutElapsed>>
        ELSE
          log[s]' = [i \in 1..Len(log[s]) |-> log[s][i] ] \o m["entries"] /\
          commitIndex[s]' = IF m["leaderCommit"] > commitIndex[s] THEN Min(m["leaderCommit"], Len(log[s]')) ELSE commitIndex[s] /\
          messages' = messages \ {m} \cup { [type |-> "AppendEntriesResponse", sender |-> s, receiver |-> m["sender"], term |-> currentTerm[s], success |-> TRUE, currentIdx |-> Len(log[s]') ] } /\
          UNCHANGED <<state, currentTerm, votedFor, lastApplied, leader, nodes, electionTimeout, timeoutElapsed>>
  ELSE IF m["type"] = "AppendEntriesResponse" THEN
    messages' = messages \ {m} /\
    UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, leader, nodes, electionTimeout, timeoutElapsed>>
AdvanceTime == 
  \E t \in Nat : 
    timeoutElapsed' = [s \in Servers |-> timeoutElapsed[s] + t] /\
    UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, leader, nodes, messages, electionTimeout>>
AddNode(n) == 
  n \in Servers \ nodes /\
  nodes' = nodes \cup {n} /\
  state[n]' = "Follower" /\
  currentTerm[n]' = 0 /\
  votedFor[n]' = None /\
  log[n]' = <<>> /\
  commitIndex[n]' = 0 /\
  lastApplied[n]' = 0 /\
  leader[n]' = None /\
  electionTimeout[n]' \in {n \in Nat : n > 0} /\
  timeoutElapsed[n]' = 0 /\
  UNCHANGED <<messages>>
RemoveNode(n) == 
  n \in nodes /\
  nodes' = nodes \ {n} /\
  UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, leader, electionTimeout, timeoutElapsed, messages>>
SnapshotBegin(s) == 
  (state[s] = "Follower" \/ state[s] = "Leader") /\
  commitIndex[s] > 0 /\
  UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, leader, nodes, electionTimeout, timeoutElapsed, messages>>
SnapshotEnd(s) == 
  log[s]' = SubSeq(log[s], commitIndex[s] + 1, Len(log[s])) /\
  UNCHANGED <<state, currentTerm, votedFor, commitIndex, lastApplied, leader, nodes, electionTimeout, timeoutElapsed, messages>>
====