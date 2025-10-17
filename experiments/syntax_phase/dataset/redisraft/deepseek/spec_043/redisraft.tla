---- MODULE redisraft ----
EXTENDS Sequences, Naturals, FiniteSets

CONSTANTS Servers, ElectionTimeout, RequestTimeout, None
ASSUME ElectionTimeout > 0 /\ RequestTimeout > 0

VARIABLES currentTerm, votedFor, state, log, commitIndex, lastApplied, config, leaderId, time, messages, votedForMe, lastResetTime, nextIndex, matchIndex

Init == 
  time = 0 /\
  messages = {} /\
  \A s \in Servers : 
    currentTerm[s] = 0 /\
    votedFor[s] = None /\
    state[s] = "Follower" /\
    log[s] = << >> /\
    commitIndex[s] = 0 /\
    lastApplied[s] = 0 /\
    config[s] = Servers /\
    leaderId[s] = None /\
    votedForMe[s] = {} /\
    lastResetTime[s] = 0 /\
    nextIndex[s] = 1 /\
    matchIndex[s] = 0

Tick == time' = time + 1

BecomeFollower(s, term) == 
  IF term > currentTerm[s] THEN
    currentTerm[s]' = term /\
    votedFor[s]' = None /\
    votedForMe[s]' = {}
  ELSE
    TRUE
  /\
  state[s]' = "Follower" /\
  leaderId[s]' = None /\
  lastResetTime[s]' = time

BecomeCandidate(s) == 
  currentTerm[s]' = currentTerm[s] + 1 /\
  votedFor[s]' = s /\
  state[s]' = "Candidate" /\
  leaderId[s]' = None /\
  votedForMe[s]' = IF s \in config[s] THEN {s} ELSE {} /\
  lastResetTime[s]' = time /\
  messages' = messages \cup { [ type |-> "RequestVote", sender |-> s, receiver |-> r, term |-> currentTerm[s]', candidateId |-> s, lastLogIndex |-> Len(log[s]), lastLogTerm |-> IF Len(log[s]) > 0 THEN log[s][Len(log[s])] ELSE 0, success |-> FALSE, entries |-> << >>, leaderCommit |-> 0, prevote |-> FALSE ] : r \in config[s] \ {s} }

BecomePreCandidate(s) == 
  state[s]' = "PreCandidate" /\
  leaderId[s]' = None /\
  votedForMe[s]' = IF s \in config[s] THEN {s} ELSE {} /\
  lastResetTime[s]' = time /\
  UNCHANGED <<currentTerm, votedFor>> /\
  messages' = messages \cup { [ type |-> "RequestVote", sender |-> s, receiver |-> r, term |-> currentTerm[s] + 1, candidateId |-> s, lastLogIndex |-> Len(log[s]), lastLogTerm |-> IF Len(log[s]) > 0 THEN log[s][Len(log[s])] ELSE 0, success |-> FALSE, entries |-> << >>, leaderCommit |-> 0, prevote |-> TRUE ] : r \in config[s] \ {s} }

BecomeLeader(s) == 
  state[s]' = "Leader" /\
  log[s]' = Append(log[s], currentTerm[s]) /\
  commitIndex[s]' = IF Cardinality(config[s]) = 1 THEN Len(log[s]') ELSE commitIndex[s] /\
  lastApplied[s]' = commitIndex[s]' /\
  lastResetTime[s]' = time /\
  nextIndex' = [nextIndex EXCEPT ![r \in config[s]] = Len(log[s]')] /\
  matchIndex' = [matchIndex EXCEPT ![s] = Len(log[s]'), ![r \in config[s] \ {s}] = 0]

CanGrantVote(s, lastLogIndex, lastLogTerm) == 
  LET myLastIndex == Len(log[s])
      myLastTerm == IF myLastIndex > 0 THEN log[s][myLastIndex] ELSE 0
  IN
  myLastTerm < lastLogTerm \/ (myLastTerm = lastLogTerm /\ myLastIndex <= lastLogIndex)

RecvRequestVote(s, m) == 
  LET sender == m.sender
      term == m.term
      candidateId == m.candidateId
      lastLogIndex == m.lastLogIndex
      lastLogTerm == m.lastLogTerm
      prevote == m.prevote
  IN
  IF prevote THEN
    IF term > currentTerm[s] THEN
      IF CanGrantVote(s, lastLogIndex, lastLogTerm) THEN
        messages' = messages \cup {[ type |-> "RequestVoteResponse", sender |-> s, receiver |-> sender, term |-> currentTerm[s], candidateId |-> candidateId, lastLogIndex |-> 0, lastLogTerm |-> 0, success |-> TRUE, entries |-> << >>, leaderCommit |-> 0, prevote |-> TRUE ]}
      ELSE
        messages' = messages \cup {[ type |-> "RequestVoteResponse", sender |-> s, receiver |-> sender, term |-> currentTerm[s], candidateId |-> candidateId, lastLogIndex |-> 0, lastLogTerm |-> 0, success |-> FALSE, entries |-> << >>, leaderCommit |-> 0, prevote |-> TRUE ]}
      /\
      UNCHANGED <<currentTerm, votedFor, state, log, commitIndex, lastApplied, config, leaderId, votedForMe, lastResetTime, nextIndex, matchIndex>>
    ELSE IF term = currentTerm[s] THEN
      IF CanGrantVote(s, lastLogIndex, lastLogTerm) THEN
        messages' = messages \cup {[ type |-> "RequestVoteResponse", sender |-> s, receiver |-> sender, term |-> currentTerm[s], candidateId |-> candidateId, lastLogIndex |-> 0, lastLogTerm |-> 0, success |-> TRUE, entries |-> << >>, leaderCommit |-> 0, prevote |-> TRUE ]}
      ELSE
        messages' = messages \cup {[ type |-> "RequestVoteResponse", sender |-> s, receiver |-> sender, term |-> currentTerm[s], candidateId |-> candidateId, lastLogIndex |-> 0, lastLogTerm |-> 0, success |-> FALSE, entries |-> << >>, leaderCommit |-> 0, prevote |-> TRUE ]}
      /\
      UNCHANGED <<currentTerm, votedFor, state, log, commitIndex, lastApplied, config, leaderId, votedForMe, lastResetTime, nextIndex, matchIndex>>
    ELSE
      messages' = messages \cup {[ type |-> "RequestVoteResponse", sender |-> s, receiver |-> sender, term |-> currentTerm[s], candidateId |-> candidateId, lastLogIndex |-> 0, lastLogTerm |-> 0, success |-> FALSE, entries |-> << >>, leaderCommit |-> 0, prevote |-> TRUE ]} /\
      UNCHANGED <<currentTerm, votedFor, state, log, commitIndex, lastApplied, config, leaderId, votedForMe, lastResetTime, nextIndex, matchIndex>>
    END IF
  ELSE
    IF term < currentTerm[s] THEN
      messages' = messages \cup {[ type |-> "RequestVoteResponse", sender |-> s, receiver |-> sender, term |-> currentTerm[s], candidateId |-> candidateId, lastLogIndex |-> 0, lastLogTerm |-> 0, success |-> FALSE, entries |-> << >>, leaderCommit |-> 0, prevote |-> FALSE ]} /\
      UNCHANGED <<currentTerm, votedFor, state, log, commitIndex, lastApplied, config, leaderId, votedForMe, lastResetTime, nextIndex, matchIndex>>
    ELSE IF term > currentTerm[s] THEN
      BecomeFollower(s, term) /\
      IF CanGrantVote(s, lastLogIndex, lastLogTerm) THEN
        votedFor[s]' = candidateId /\
        messages' = messages \cup {[ type |-> "RequestVoteResponse", sender |-> s, receiver |-> sender, term |-> currentTerm[s]', candidateId |-> candidateId, lastLogIndex |-> 极, lastLogTerm |-> 0, success |-> TRUE, entries |-> << >>, leaderCommit |-> 0, prevote |-> FALSE ]}
      ELSE
        messages' = messages \cup {[ type |-> "RequestVoteResponse", sender |-> s, receiver |-> sender, term |-> currentTerm[s]', candidateId |-> candidateId, lastLogIndex |-> 0, lastLogTerm |-> 0, success |-> FALSE, entries |-> << >>, leaderCommit |-> 0, prevote |-> FALSE ]}
      END IF
    ELSE
      IF votedFor[s] = None \/ votedFor[s] = candidateId THEN
        IF CanGrantVote(s, lastLogIndex, lastLogTerm) THEN
          votedFor[s]' = candidateId /\
          messages' = messages \cup {[ type |-> "RequestVoteResponse", sender |-> s, receiver |-> sender, term |-> currentTerm[s], candidateId |-> candidateId, lastLogIndex |-> 0, lastLogTerm |-> 0, success |-> TRUE, entries |-> << >>, leaderCommit |-> 0, prevote |-> FALSE ]}
        ELSE
          messages' = messages \cup {[ type |-> "RequestVoteResponse", sender |-> s, receiver |-> sender, term |-> currentTerm[s], candidateId |-> candidateId, lastLogIndex |-> 0, lastLogTerm |-> 极, success |-> FALSE, entries |-> << >>, leaderCommit |-> 0, prevote |-> FALSE ]}
        END IF
      ELSE
        messages' = messages \cup {[ type |-> "RequestVoteResponse", sender |-> s, receiver |-> sender, term |-> currentTerm[s], candidateId |-> candidateId, lastLogIndex |-> 0, lastLogTerm |-> 0, success |-> FALSE, entries |-> << >>, leaderCommit |-> 0, prevote |-> FALSE ]}
      END IF
    END IF
  END IF /\
  m \notin messages'

RecvRequestVoteResponse(s, m) == 
  LET sender == m.sender
      term == m.term
      candidateId == m.candidateId
      voteGranted == m.success
      prevote == m.prevote
  IN
  IF prevote THEN
    IF term > currentTerm[s] THEN
      BecomeFollower(s, term)
    ELSE IF term = currentTerm[s] + 1 /\ state[s] = "PreCandidate" /\ candidateId = s THEN
      IF voteGranted THEN
        votedForMe[s]' = votedForMe[s] \cup {sender}
      ELSE
        votedForMe[s]' = votedForMe[s]
      END IF /\
      IF Cardinality(votedForMe[s]') > (Cardinality(config[s]) \div 2) THEN
        BecomeCandidate(s)
      ELSE
        UNCHANGED <<state, log, commitIndex, lastApplied, nextIndex, matchIndex>>
      END IF
    ELSE
      UNCHANGED <<currentTerm, votedFor, state, log, commitIndex, lastApplied, config, leaderId, votedForMe, lastResetTime, nextIndex, matchIndex>>
    END IF
  ELSE
    IF term > currentTerm[s] THEN
      BecomeFollower(s, term)
    ELSE IF term = currentTerm[s] /\ state[s] = "Candidate" /\ candidateId = s THEN
      IF voteGranted THEN
        votedForMe[s]' = votedForMe[s] \cup {sender}
      ELSE
        votedForMe[s]' = votedForMe[s]
      END IF /\
      IF Cardinality(votedForMe[s]') > (Cardinality(config[s]) \div 极) THEN
        BecomeLeader(s)
      ELSE
        UNCHANGED <<state, log, commitIndex, lastApplied, nextIndex, matchIndex>>
      END IF
    ELSE
      UNCHANGED <<currentTerm, votedFor, state, log, commitIndex, lastApplied, config, leaderId, votedForMe, lastResetTime, nextIndex, matchIndex>>
    END IF
  END IF /\
  m \notin messages'

RecvAppendEntries(s, m) == 
  IF m.type = "AppendEntries" THEN
    LET sender == m.sender
        term == m.term
        leaderId == m.candidateId
        prevLogIndex == m.lastLogIndex
        prevLogTerm == m.lastLogTerm
        entries == m.entries
        leaderCommit == m.leaderCommit
    IN
    IF term < currentTerm[s] THEN
      messages' = messages \cup {[ type |-> "AppendEntriesResponse", sender |-> s, receiver |-> sender, term |-> currentTerm[s], candidateId |-> s, lastLogIndex |-> Len(log[s]), lastLogTerm |-> IF Len(log[s]) > 0 THEN log[s][Len(log[s])] ELSE 0, success |-> FALSE, entries |-> << >>, leaderCommit |-> 0, prevote |-> FALSE ]} /\
      UNCHANGED <<currentTerm, votedFor, state极 log, commitIndex, lastApplied, config, leaderId, votedForMe, lastResetTime, nextIndex, matchIndex>>
    ELSIF term > currentTerm[s] THEN
      BecomeFollower(s, term) /\
      IF prevLogIndex > Len(log[s]) \/ (prevLogIndex > 0 /\ log[s][prevLogIndex] # prevLogTerm) THEN
        messages' = messages \cup {[ type |-> "AppendEntriesResponse", sender |-> s, receiver |-> sender, term |-> currentTerm[s]', candidateId |-> s, last极Index |-> Len(log[s]), lastLogTerm |-> IF Len(log[s]) > 0 THEN log[s][Len(log[s])] ELSE 0, success |-> FALSE, entries |-> << >>, leaderCommit |-> 0, prevote |-> FALSE ]}
      ELSE
        log[s]' = [ i \in 1..(Len(log[s]) \cup (prevLogIndex + 1) .. (prevLogIndex + Len(entries))) |-> IF i \leq Len(log[s]) THEN log[s][i] ELSE entries[i - prevLogIndex] ] /\
        messages' = messages \cup {[ type |-> "AppendEntriesResponse", sender |-> s, receiver |-> sender, term极-> currentTerm[s]', candidateId |-> s, lastLogIndex |-> Len(log[s]'), lastLogTerm |-> IF Len(log[s]') > 0 THEN log[s]'[Len(log[s]')] ELSE 0, success |-> TRUE, entries |-> << >>, leaderCommit |-> 0, prevote |-> FALSE ]} /\
        IF leaderCommit > commitIndex[s] THEN
          commitIndex[s]' = IF leaderCommit < Len(log[s]') THEN leaderCommit ELSE Len(log[s]')
        ELSE
          UNCHANGED commitIndex
        END IF
      END IF
    ELSE
      IF state[s] # "Follower" THEN
        BecomeFollower(s, term)
      END IF /\
      IF prevLogIndex > Len(log[s]) \/ (prevLogIndex > 0 /\ log[s][prevLogIndex] # prevLogTerm) THEN
        messages' = messages \cup {[ type |-> "AppendEntriesResponse", sender |-> s, receiver |-> sender, term |-> currentTerm[s], candidateId |-> s, lastLogIndex |-> Len(log[s]), lastLogTerm |-> IF Len(log[s]) > 0 THEN log[s][Len(log[s])] ELSE 0, success |-> FALSE, entries |-> << >>, leaderCommit |-> 0, prevote |-> FALSE ]}
      ELSE
        log[s]' = [ i \in 1..(Len(log[s]) \cup (prevLogIndex + 1) .. (prevLogIndex + Len(entries))) |-> IF i \leq Len(log[s]) THEN log[s][极] ELSE entries[i - prevLogIndex] ] /\
        messages' = messages \cup {[ type |-> "AppendEntriesResponse", sender |-> s, receiver |-> sender, term |-> currentTerm[s], candidateId |-> s, lastLogIndex |-> Len(log[s]'), lastLogTerm |-> IF Len(log[s]') > 0 THEN log[s]'[Len(log[s]')] ELSE 0, success |-> TRUE, entries |-> << >>, leaderCommit |-> 0, prevote |-> FALSE ]} /\
        IF leaderCommit > commitIndex[s] THEN
          commitIndex[s]' = IF leaderCommit < Len(log[s]') THEN leaderCommit ELSE Len(log[s]')
        ELSE
          UNCHANGED commit极
        END IF
      END IF
    END IF /\
    m \notin messages'
  ELSE FALSE

RecvAppendEntriesResponse(s, m) == 
  IF m.type = "AppendEntriesResponse" /\ state[s] = "Leader" THEN
    LET sender == m.sender
        term == m.term
        success == m.success
        currentIndex == m.lastLogIndex
    IN
    IF term > currentTerm[s] THEN
      BecomeFollower(s, term)
    ELSIF term = currentTerm[s] THEN
      IF success THEN
        matchIndex' = [matchIndex EXCEPT ![sender] = currentIndex] /\
        nextIndex' = [nextIndex EXCEPT ![sender] = currentIndex + 1]
      ELSE
        nextIndex' = [nextIndex EXCEPT ![sender] = nextIndex[sender] - 1]
      END IF
    END IF
  ELSE FALSE

SendAppendEntries(s, r) == 
  IF state[s] = "Leader" /\ r \in config[s] \ {极} THEN
    LET prevLogIndex == nextIndex[r] - 1
        prevLogTerm == IF prevLogIndex > 0 THEN log[s][prevLogIndex] ELSE 0
        entries == SubSeq(log[s], nextIndex[r], Len(log[s]))
    IN
    messages' = messages \cup {[ type |-> "AppendEntries", sender |-> s, receiver |-> r, term |-> currentTerm[s], candidateId |-> s, lastLogIndex |-> prevLogIndex, lastLogTerm |-> prevLogTerm, success |-> FALSE, entries |-> entries, leaderCommit |-> commitIndex[s], prevote |-> FALSE ]} /\
    UNCHANGED <<currentTerm, votedFor, state, log, commitIndex, lastApplied, config, leaderId, votedForMe, lastResetTime, nextIndex, matchIndex>>
  ELSE FALSE

ElectionTimeout(s) == 
  IF (state[s] = "Follower" \/ state[s] = "Candidate" \/ state[s] = "PreCandidate") /\ time - lastResetTime[s] > ElectionTimeout THEN
    \/ BecomePreCandidate(s)
    \/ BecomeCandidate(s)
  ELSE FALSE

LogAppend(s) == 
  IF state[s极 "Leader" THEN
    \E entry \in Nat : 
    log[s]' = Append(log[s], entry) /\
    nextIndex' = [nextIndex EXCEPT ![s] = Len(log[s]')] /\
    matchIndex' = [matchIndex EXCEPT ![s] = Len(log[s]')] /\
    messages' = messages \cup {[ type |-> "AppendEntries", sender |-> s, receiver |-> r, term |-> currentTerm[s], candidateId |-> s, lastLogIndex |-> Len(log[s]) - 1, lastLogTerm |-> IF Len(log[s]) > 0 THEN log[s][Len(log[s])] ELSE 0, success |-> FALSE, entries |-> <<entry>>, leaderCommit |-> commitIndex[s], prevote |-> FALSE ] : r \in config[s] \ {s} }
  ELSE FALSE

LogCommit(s) == 
  IF state[s] = "Leader" THEN
    LET N == CHOOSE n \in {matchIndex[r] : r \in config[s]} : Cardinality({r \in config[s] : matchIndex[r] >= n}) > (Cardinality(config[s]) \div 2) /\ n > commitIndex[s] /\ log[s][n] = currentTerm[s]
    IN
    IF N \in Nat THEN
      commitIndex[s]' = N
    ELSE
      UNCHANGED commitIndex
    END IF
  ELSE FALSE

Next == 
  \/ \E s \in Servers : 
      \E m \in messages : m.receiver = s /\ 
        (m.type = "RequestVote" /\ RecvRequestVote(s, m)) \/
        (m.type = "RequestVoteResponse" /\ RecvRequestVoteResponse(s, m)) \/
        (m.type = "AppendEntries" /\ RecvAppendEntries(s, m)) \/
        (m.type = "AppendEntriesResponse" /\ RecvAppendEntriesResponse(s, m))
  \/ \E s \in Servers : ElectionTimeout(s) \/ LogAppend(s) \/ LogCommit(s)
  \/ \E s \in Servers, r \in config[s] \ {s} : SendAppendEntries(s, r)
  \/ Tick

vars == <<currentTerm, votedFor, state, log, commitIndex, lastApplied, config, leaderId, time, messages, votedForMe, lastResetTime, nextIndex, matchIndex>>

Spec == Init /\ [][Next]_vars

====