---- MODULE redisraft ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags, Integers

CONSTANTS
  Node,
  NoNode,
  ELECTION_BASE,
  REQUEST_TIMEOUT,
  FOLLOWER, PRECANDIDATE, CANDIDATE, LEADER,
  NO_OP, ADD_NODE, ADD_NONVOTING_NODE, REMOVE_NODE, NORMAL

ET == {NO_OP, ADD_NODE, ADD_NONVOTING_NODE, REMOVE_NODE, NORMAL}
ETRange == { i \in Nat : ELECTION_BASE <= i /\ i <= 2 * ELECTION_BASE }

VARIABLES
  state,
  currentTerm,
  votedFor,
  leaderId,
  log,
  commitIndex,
  lastApplied,
  lastAppliedTerm,
  electionTimeoutRand,
  requestTimeout,
  timeoutElapsed,
  nextIndex,
  matchIndex,
  snapshotLastIdx,
  snapshotLastTerm,
  snapshotInProgress,
  nextSnapshotLastIdx,
  nextSnapshotLastTerm,
  votingCfgChangeLogIdx,
  nodes,
  pending,
  preVotes,
  votes,
  conflictDeleteIdx

vars == << state, currentTerm, votedFor, leaderId, log, commitIndex, lastApplied, lastAppliedTerm, electionTimeoutRand, requestTimeout, timeoutElapsed, nextIndex, matchIndex, snapshotLastIdx, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIdx, nextSnapshotLastTerm, votingCfgChangeLogIdx, nodes, pending, preVotes, votes, conflictDeleteIdx >>

Entry(term, type, node) == [term |-> term, type |-> type, node |-> node]

VotingSet == { i \in Node : nodes[i].active /\ nodes[i].voting }
ActiveSet == { i \in Node : nodes[i].active }
IsMajority(S) == 2 * Cardinality(S) > Cardinality(VotingSet)

LastIndex(n) == snapshotLastIdx[n] + Len(log[n])
LastTerm(n) == IF Len(log[n]) > 0 THEN log[n][Len(log[n])].term ELSE snapshotLastTerm[n]

TermAt(n, i) ==
  IF i = snapshotLastIdx[n] THEN snapshotLastTerm[n]
  ELSE IF snapshotLastIdx[n] < i /\ i <= LastIndex(n) THEN log[n][i - snapshotLastIdx[n]].term
  ELSE 0

HasEntryAt(n, i) == snapshotLastIdx[n] < i /\ i <= LastIndex(n)

GetEntries(n, startIdx, endIdx) ==
  IF startIdx > endIdx THEN << >>
  ELSE [k \in 1..(endIdx - startIdx + 1) |-> log[n][startIdx - snapshotLastIdx[n] + k - 1]]

AppendAll(s, t) == [i \in 1..(Len(s) + Len(t)) |-> IF i <= Len(s) THEN s[i] ELSE t[i - Len(s)]]

MessageKinds == {"AE","AEResp","RV","RVResp"}

\* Minimal fix: Define Min/Max for set and binary forms
Min(S) == CHOOSE x \in S : \A y \in S : x <= y
Max(S) == CHOOSE x \in S : \A y \in S : x >= y
Min(a, b) == IF a <= b THEN a ELSE b
Max(a, b) == IF a >= b THEN a ELSE b

Init ==
  /\ state = [n \in Node |-> FOLLOWER]
  /\ currentTerm = [n \in Node |-> 0]
  /\ votedFor = [n \in Node |-> NoNode]
  /\ leaderId = [n \in Node |-> NoNode]
  /\ log = [n \in Node |-> << >>]
  /\ commitIndex = [n \in Node |-> 0]
  /\ lastApplied = [n \in Node |-> 0]
  /\ lastAppliedTerm = [n \in Node |-> 0]
  /\ electionTimeoutRand \in [Node -> ETRange]
  /\ requestTimeout = [n \in Node |-> REQUEST_TIMEOUT]
  /\ timeoutElapsed = [n \in Node |-> 0]
  /\ nextIndex = [l \in Node |-> [p \in Node |-> 1]]
  /\ matchIndex = [l \in Node |-> [p \in Node |-> 0]]
  /\ snapshotLastIdx = [n \in Node |-> 0]
  /\ snapshotLastTerm = [n \in Node |-> 0]
  /\ snapshotInProgress = [n \in Node |-> FALSE]
  /\ nextSnapshotLastIdx = [n \in Node |-> 0]
  /\ nextSnapshotLastTerm = [n \in Node |-> 0]
  /\ votingCfgChangeLogIdx = [n \in Node |-> 0]
  /\ nodes = [i \in Node |-> [active |-> TRUE, voting |-> TRUE, votingCommitted |-> TRUE, additionCommitted |-> TRUE, hasSufficientLogs |-> TRUE]]
  /\ pending = << >>
  /\ preVotes = [n \in Node |-> {}]
  /\ votes = [n \in Node |-> {}]
  /\ conflictDeleteIdx = [n \in Node |-> 0]

BecomeFollower(n) ==
  /\ n \in Node
  /\ state[n] # FOLLOWER
  /\ state' = [state EXCEPT ![n] = FOLLOWER]
  /\ electionTimeoutRand' = [electionTimeoutRand EXCEPT ![n] = CHOOSE k \in ETRange : TRUE]
  /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![n] = 0]
  /\ leaderId' = [leaderId EXCEPT ![n] = NoNode]
  /\ UNCHANGED << currentTerm, votedFor, log, commitIndex, lastApplied, lastAppliedTerm, requestTimeout, nextIndex, matchIndex, snapshotLastIdx, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIdx, nextSnapshotLastTerm, votingCfgChangeLogIdx, nodes, pending, preVotes, votes, conflictDeleteIdx >>

BecomePreCandidate(n) ==
  /\ n \in Node
  /\ state[n] # LEADER
  /\ state' = [state EXCEPT ![n] = PRECANDIDATE]
  /\ preVotes' = [preVotes EXCEPT ![n] = {}]
  /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![n] = 0]
  /\ UNCHANGED << currentTerm, votedFor, leaderId, log, commitIndex, lastApplied, lastAppliedTerm, electionTimeoutRand, requestTimeout, nextIndex, matchIndex, snapshotLastIdx, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIdx, nextSnapshotLastTerm, votingCfgChangeLogIdx, nodes, pending, votes, conflictDeleteIdx >>

BecomeCandidate(n) ==
  /\ n \in Node
  /\ state[n] = PRECANDIDATE \/ state[n] = FOLLOWER \/ state[n] = CANDIDATE
  /\ state[n] # LEADER
  /\ currentTerm' = [currentTerm EXCEPT ![n] = currentTerm[n] + 1]
  /\ votedFor' = [votedFor EXCEPT ![n] = IF nodes[n].voting THEN n ELSE NoNode]
  /\ votes' = [votes EXCEPT ![n] = IF nodes[n].voting THEN {n} ELSE {}]
  /\ state' = [state EXCEPT ![n] = CANDIDATE]
  /\ leaderId' = [leaderId EXCEPT ![n] = NoNode]
  /\ electionTimeoutRand' = [electionTimeoutRand EXCEPT ![n] = CHOOSE k \in ETRange : TRUE]
  /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![n] = 0]
  /\ UNCHANGED << log, commitIndex, lastApplied, lastAppliedTerm, requestTimeout, nextIndex, matchIndex, snapshotLastIdx, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIdx, nextSnapshotLastTerm, votingCfgChangeLogIdx, nodes, pending, preVotes, conflictDeleteIdx >>

BecomeLeader(n) ==
  /\ n \in Node
  /\ state[n] = CANDIDATE
  /\ IsMajority(votes[n])
  /\ LET newEntry == Entry(currentTerm[n], NO_OP, NoNode) IN
     LET newLog == [log EXCEPT ![n] = Append(log[n], newEntry)] IN
     LET newLastIdx == snapshotLastIdx[n] + Len(newLog[n]) IN
     /\ log' = newLog
     /\ state' = [state EXCEPT ![n] = LEADER]
     /\ leaderId' = [leaderId EXCEPT ![n] = n]
     /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![n] = 0]
     /\ nextIndex' = [nextIndex EXCEPT ![n] = [p \in Node |-> newLastIdx + 1]]
     /\ matchIndex' = [matchIndex EXCEPT ![n] = [p \in Node |-> IF p = n THEN newLastIdx ELSE 0]]
  /\ UNCHANGED << currentTerm, votedFor, commitIndex, lastApplied, lastAppliedTerm, electionTimeoutRand, requestTimeout, snapshotLastIdx, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIdx, nextSnapshotLastTerm, votingCfgChangeLogIdx, nodes, pending, preVotes, votes, conflictDeleteIdx >>

SendRequestVote(c, p) ==
  /\ c \in Node /\ p \in Node /\ c # p
  /\ nodes[p].voting /\ nodes[p].active
  /\ state[c] = PRECANDIDATE \/ state[c] = CANDIDATE
  /\ LET pv == (state[c] = PRECANDIDATE) IN
     LET t == IF pv THEN currentTerm[c] + 1 ELSE currentTerm[c] IN
     LET msg == [kind |-> "RV", from |-> c, to |-> p, prevote |-> pv, term |-> t, lastIndex |-> LastIndex(c), lastTerm |-> LastTerm(c)] IN
     /\ pending' = Append(pending, msg)
     /\ UNCHANGED << state, currentTerm, votedFor, leaderId, log, commitIndex, lastApplied, lastAppliedTerm, electionTimeoutRand, requestTimeout, timeoutElapsed, nextIndex, matchIndex, snapshotLastIdx, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIdx, nextSnapshotLastTerm, votingCfgChangeLogIdx, nodes, preVotes, votes, conflictDeleteIdx >>

RecvRequestVote ==
  \E i \in 1..Len(pending) :
    LET m == pending[i] IN
    /\ m.kind = "RV"
    /\ m.to \in Node
    /\ LET r == m.to IN
       LET upToDate == (m.lastTerm > LastTerm(r)) \/ (m.lastTerm = LastTerm(r) /\ m.lastIndex >= LastIndex(r)) IN
       LET leaderOk == ~(m.prevote /\ leaderId[r] # NoNode /\ leaderId[r] # m.from /\ timeoutElapsed[r] < electionTimeoutRand[r]) IN
       LET termAdv == (~m.prevote /\ m.term > currentTerm[r]) IN
       LET curTerm == IF termAdv THEN m.term ELSE currentTerm[r] IN
       LET st == IF termAdv THEN FOLLOWER ELSE state[r] IN
       LET canVote ==
         IF m.prevote THEN upToDate /\ leaderOk
         ELSE (curTerm = m.term /\ upToDate /\ (votedFor[r] = NoNode \/ votedFor[r] = m.from)) IN
       LET grant == canVote /\ curTerm = m.term IN
       LET resp == [kind |-> "RVResp", from |-> r, to |-> m.from, prevote |-> m.prevote, requestTerm |-> m.term, term |-> curTerm, voteGranted |-> grant] IN
       /\ pending' = Append(RemoveAt(pending, i), resp)
       /\ currentTerm' = [currentTerm EXCEPT ![r] = curTerm]
       /\ state' = [state EXCEPT ![r] = st]
       /\ votedFor' = [votedFor EXCEPT ![r] = IF ~m.prevote /\ canVote THEN m.from ELSE votedFor[r]]
       /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![r] = IF ~m.prevote /\ canVote THEN 0 ELSE timeoutElapsed[r]]
       /\ leaderId' = [leaderId EXCEPT ![r] = IF ~m.prevote /\ canVote THEN NoNode ELSE leaderId[r]]
       /\ UNCHANGED << log, commitIndex, lastApplied, lastAppliedTerm, electionTimeoutRand, requestTimeout, nextIndex, matchIndex, snapshotLastIdx, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIdx, nextSnapshotLastTerm, votingCfgChangeLogIdx, nodes, preVotes, votes, conflictDeleteIdx >>

RecvRequestVoteResponse ==
  \E i \in 1..Len(pending) :
    LET m == pending[i] IN
    /\ m.kind = "RVResp"
    /\ m.to \in Node
    /\ LET n == m.to IN
       LET higher == (m.term > currentTerm[n]) IN
       /\ IF higher THEN
            /\ currentTerm' = [currentTerm EXCEPT ![n] = m.term]
            /\ state' = [state EXCEPT ![n] = FOLLOWER]
            /\ votedFor' = [votedFor EXCEPT ![n] = NoNode]
            /\ pending' = RemoveAt(pending, i)
            /\ UNCHANGED << leaderId, log, commitIndex, lastApplied, lastAppliedTerm, electionTimeoutRand, requestTimeout, timeoutElapsed, nextIndex, matchIndex, snapshotLastIdx, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIdx, nextSnapshotLastTerm, votingCfgChangeLogIdx, nodes, preVotes, votes, conflictDeleteIdx >>
          ELSE
            LET validPrevote == (m.prevote /\ state[n] = PRECANDIDATE /\ m.requestTerm = currentTerm[n] + 1) IN
            LET validVote == (~m.prevote /\ state[n] = CANDIDATE /\ m.requestTerm = currentTerm[n]) IN
            /\ pending' = RemoveAt(pending, i)
            /\ IF m.voteGranted /\ validPrevote THEN
                 /\ preVotes' = [preVotes EXCEPT ![n] = preVotes[n] \cup {m.from}]
                 /\ UNCHANGED << state, currentTerm, votedFor, leaderId, log, commitIndex, lastApplied, lastAppliedTerm, electionTimeoutRand, requestTimeout, timeoutElapsed, nextIndex, matchIndex, snapshotLastIdx, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIdx, nextSnapshotLastTerm, votingCfgChangeLogIdx, nodes, votes, conflictDeleteIdx >>
               ELSE IF m.voteGranted /\ validVote THEN
                 /\ votes' = [votes EXCEPT ![n] = votes[n] \cup {m.from}]
                 /\ UNCHANGED << state, currentTerm, votedFor, leaderId, log, commitIndex, lastApplied, lastAppliedTerm, electionTimeoutRand, requestTimeout, timeoutElapsed, nextIndex, matchIndex, snapshotLastIdx, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIdx, nextSnapshotLastTerm, votingCfgChangeLogIdx, nodes, preVotes, conflictDeleteIdx >>
               ELSE
                 /\ UNCHANGED vars

SendAppendEntries(l, f, k) ==
  /\ l \in Node /\ f \in Node /\ l # f
  /\ state[l] = LEADER
  /\ nodes[f].active
  /\ nextIndex[l][f] > snapshotLastIdx[l]
  /\ LastIndex(l) >= nextIndex[l][f]
  /\ k \in 1..(LastIndex(l) - nextIndex[l][f] + 1)
  /\ LET prevIdx == nextIndex[l][f] - 1 IN
     LET prevTerm == TermAt(l, prevIdx) IN
     LET ents == GetEntries(l, nextIndex[l][f], nextIndex[l][f] + k - 1) IN
     LET msg == [kind |-> "AE", from |-> l, to |-> f, term |-> currentTerm[l], prevIndex |-> prevIdx, prevTerm |-> prevTerm, entries |-> ents, leaderCommit |-> commitIndex[l]] IN
     /\ pending' = Append(pending, msg)
     /\ UNCHANGED << state, currentTerm, votedFor, leaderId, log, commitIndex, lastApplied, lastAppliedTerm, electionTimeoutRand, requestTimeout, timeoutElapsed, nextIndex, matchIndex, snapshotLastIdx, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIdx, nextSnapshotLastTerm, votingCfgChangeLogIdx, nodes, preVotes, votes, conflictDeleteIdx >>

SendHeartbeat(l, f) ==
  /\ l \in Node /\ f \in Node /\ l # f
  /\ state[l] = LEADER
  /\ nodes[f].active
  /\ LET prevIdx == nextIndex[l][f] - 1 IN
     LET prevTerm == TermAt(l, prevIdx) IN
     LET msg == [kind |-> "AE", from |-> l, to |-> f, term |-> currentTerm[l], prevIndex |-> prevIdx, prevTerm |-> prevTerm, entries |-> << >>, leaderCommit |-> commitIndex[l]] IN
     /\ pending' = Append(pending, msg)
     /\ UNCHANGED << state, currentTerm, votedFor, leaderId, log, commitIndex, lastApplied, lastAppliedTerm, electionTimeoutRand, requestTimeout, timeoutElapsed, nextIndex, matchIndex, snapshotLastIdx, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIdx, nextSnapshotLastTerm, votingCfgChangeLogIdx, nodes, preVotes, votes, conflictDeleteIdx >>

RecvAppendEntries ==
  \E i \in 1..Len(pending) :
    LET m == pending[i] IN
    /\ m.kind = "AE"
    /\ m.to \in Node
    /\ LET r == m.to IN
       LET termAdv == (m.term > currentTerm[r]) IN
       LET curTerm == IF termAdv THEN m.term ELSE currentTerm[r] IN
       LET st == IF termAdv THEN FOLLOWER ELSE state[r] IN
       LET rejectLow == (m.term < currentTerm[r]) IN
       LET prevOK ==
         (m.prevIndex = snapshotLastIdx[r] /\ m.prevTerm = snapshotLastTerm[r])
         \/ (HasEntryAt(r, m.prevIndex) /\ TermAt(r, m.prevIndex) = m.prevTerm) IN
       LET conflictSet == { j \in 1..Len(m.entries) :
                             LET abs == m.prevIndex + j IN
                               HasEntryAt(r, abs) /\ TermAt(r, abs) # m.entries[j].term } IN
       LET confIdx == IF conflictSet = {} THEN 0 ELSE (m.prevIndex + Min(conflictSet)) IN
       /\ IF rejectLow THEN
            /\ pending' = RemoveAt(pending, i)
            /\ currentTerm' = currentTerm
            /\ state' = state
            /\ UNCHANGED << votedFor, leaderId, log, commitIndex, lastApplied, lastAppliedTerm, electionTimeoutRand, requestTimeout, timeoutElapsed, nextIndex, matchIndex, snapshotLastIdx, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIdx, nextSnapshotLastTerm, votingCfgChangeLogIdx, nodes, preVotes, votes, conflictDeleteIdx >>
          ELSE
            /\ currentTerm' = [currentTerm EXCEPT ![r] = curTerm]
            /\ state' = [state EXCEPT ![r] = st]
            /\ IF ~prevOK THEN
                 /\ pending' = Append(RemoveAt(pending, i), [kind |-> "AEResp", from |-> r, to |-> m.from, term |-> curTerm, success |-> FALSE, currentIdx |-> LastIndex(r)])
                 /\ conflictDeleteIdx' = [conflictDeleteIdx EXCEPT ![r] = Max(conflictDeleteIdx[r], m.prevIndex)]
                 /\ UNCHANGED << votedFor, leaderId, log, commitIndex, lastApplied, lastAppliedTerm, electionTimeoutRand, requestTimeout, timeoutElapsed, nextIndex, matchIndex, snapshotLastIdx, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIdx, nextSnapshotLastTerm, votingCfgChangeLogIdx, nodes, preVotes, votes >>
               ELSE
                 /\ leaderId' = [leaderId EXCEPT ![r] = m.from]
                 /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![r] = 0]
                 /\ IF confIdx # 0 /\ confIdx > commitIndex[r] THEN
                      /\ pending' = Append(RemoveAt(pending, i), [kind |-> "AEResp", from |-> r, to |-> m.from, term |-> curTerm, success |-> FALSE, currentIdx |-> LastIndex(r)])
                      /\ conflictDeleteIdx' = [conflictDeleteIdx EXCEPT ![r] = Max(conflictDeleteIdx[r], confIdx)]
                      /\ UNCHANGED << votedFor, log, commitIndex, lastApplied, lastAppliedTerm, electionTimeoutRand, requestTimeout, nextIndex, matchIndex, snapshotLastIdx, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIdx, nextSnapshotLastTerm, votingCfgChangeLogIdx, nodes, preVotes, votes >>
                    ELSE
                      /\ LET need == Max(0, Len(m.entries) - (LastIndex(r) - m.prevIndex)) IN
                         LET newEnts == SubSeq(m.entries, Len(m.entries) - need + 1, Len(m.entries)) IN
                         LET newLog == [log EXCEPT ![r] = AppendAll(log[r], newEnts)] IN
                         LET newLastIdx == snapshotLastIdx[r] + Len(newLog[r]) IN
                         /\ log' = newLog
                         /\ commitIndex' = [commitIndex EXCEPT ![r] = Min(m.leaderCommit, newLastIdx)]
                         /\ pending' = Append(RemoveAt(pending, i), [kind |-> "AEResp", from |-> r, to |-> m.from, term |-> curTerm, success |-> TRUE, currentIdx |-> newLastIdx])
                         /\ UNCHANGED << votedFor, lastApplied, lastAppliedTerm, electionTimeoutRand, requestTimeout, nextIndex, matchIndex, snapshotLastIdx, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIdx, nextSnapshotLastTerm, votingCfgChangeLogIdx, nodes, preVotes, votes, conflictDeleteIdx >>

RecvAppendEntriesResponse ==
  \E i \in 1..Len(pending) :
    LET m == pending[i] IN
    /\ m.kind = "AEResp"
    /\ m.to \in Node /\ m.from \in Node
    /\ LET l == m.to IN
       /\ pending' = RemoveAt(pending, i)
       /\ IF m.term > currentTerm[l] THEN
            /\ currentTerm' = [currentTerm EXCEPT ![l] = m.term]
            /\ state' = [state EXCEPT ![l] = FOLLOWER]
            /\ votedFor' = [votedFor EXCEPT ![l] = NoNode]
            /\ UNCHANGED << leaderId, log, commitIndex, lastApplied, lastAppliedTerm, electionTimeoutRand, requestTimeout, timeoutElapsed, nextIndex, matchIndex, snapshotLastIdx, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIdx, nextSnapshotLastTerm, votingCfgChangeLogIdx, nodes, preVotes, votes, conflictDeleteIdx >>
          ELSE
            /\ IF state[l] # LEADER THEN
                 /\ UNCHANGED vars
               ELSE
                 /\ IF ~m.success THEN
                      /\ nextIndex' = [nextIndex EXCEPT ![l] = [p \in Node |-> IF p = m.from THEN Max(1, Min(m.currentIdx + 1, LastIndex(l) + 1)) ELSE nextIndex[l][p]]]
                      /\ UNCHANGED << state, currentTerm, votedFor, leaderId, log, commitIndex, lastApplied, lastAppliedTerm, electionTimeoutRand, requestTimeout, timeoutElapsed, matchIndex, snapshotLastIdx, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIdx, nextSnapshotLastTerm, votingCfgChangeLogIdx, nodes, preVotes, votes, conflictDeleteIdx >>
                    ELSE
                      /\ matchIndex' = [matchIndex EXCEPT ![l] = [p \in Node |-> IF p = m.from THEN Max(matchIndex[l][p], m.currentIdx) ELSE matchIndex[l][p]]]
                      /\ nextIndex' = [nextIndex EXCEPT ![l] = [p \in Node |-> IF p = m.from THEN matchIndex'[l][p] + 1 ELSE nextIndex[l][p]]]
                      /\ UNCHANGED << state, currentTerm, votedFor, leaderId, log, commitIndex, lastApplied, lastAppliedTerm, electionTimeoutRand, requestTimeout, timeoutElapsed, snapshotLastIdx, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIdx, nextSnapshotLastTerm, votingCfgChangeLogIdx, nodes, preVotes, votes, conflictDeleteIdx >>

ElectionStart(n) ==
  /\ n \in Node
  /\ state[n] # LEADER
  /\ timeoutElapsed[n] >= electionTimeoutRand[n]
  /\ state' = [state EXCEPT ![n] = PRECANDIDATE]
  /\ leaderId' = [leaderId EXCEPT ![n] = NoNode]
  /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![n] = 0]
  /\ electionTimeoutRand' = [electionTimeoutRand EXCEPT ![n] = CHOOSE k \in ETRange : TRUE]
  /\ preVotes' = [preVotes EXCEPT ![n] = {}]
  /\ UNCHANGED << currentTerm, votedFor, log, commitIndex, lastApplied, lastAppliedTerm, requestTimeout, nextIndex, matchIndex, snapshotLastIdx, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIdx, nextSnapshotLastTerm, votingCfgChangeLogIdx, nodes, pending, votes, conflictDeleteIdx >>

ElectionTimeout(n) ==
  /\ n \in Node
  /\ state[n] # LEADER
  /\ timeoutElapsed[n] >= electionTimeoutRand[n]
  /\ UNCHANGED vars

LogAppend(l) ==
  /\ l \in Node
  /\ state[l] = LEADER
  /\ LET e == Entry(currentTerm[l], NORMAL, NoNode) IN
     /\ log' = [log EXCEPT ![l] = Append(log[l], e)]
     /\ UNCHANGED << state, currentTerm, votedFor, leaderId, commitIndex, lastApplied, lastAppliedTerm, electionTimeoutRand, requestTimeout, timeoutElapsed, nextIndex, matchIndex, snapshotLastIdx, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIdx, nextSnapshotLastTerm, votingCfgChangeLogIdx, nodes, pending, preVotes, votes, conflictDeleteIdx >>

LogDelete(n) ==
  /\ n \in Node
  /\ conflictDeleteIdx[n] # 0
  /\ conflictDeleteIdx[n] > commitIndex[n]
  /\ conflictDeleteIdx[n] <= LastIndex(n)
  /\ LET k == conflictDeleteIdx[n] - snapshotLastIdx[n] - 1 IN
     /\ log' = [log EXCEPT ![n] = SubSeq(log[n], 1, k)]
     /\ conflictDeleteIdx' = [conflictDeleteIdx EXCEPT ![n] = 0]
     /\ UNCHANGED << state, currentTerm, votedFor, leaderId, commitIndex, lastApplied, lastAppliedTerm, electionTimeoutRand, requestTimeout, timeoutElapsed, nextIndex, matchIndex, snapshotLastIdx, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIdx, nextSnapshotLastTerm, votingCfgChangeLogIdx, nodes, pending, preVotes, votes >>

LogCommit(l, c) ==
  /\ l \in Node
  /\ state[l] = LEADER
  /\ commitIndex[l] < c /\ c <= LastIndex(l)
  /\ TermAt(l, c) = currentTerm[l]
  /\ IsMajority({ p \in VotingSet : (p = l /\ matchIndex[l][p] >= c) \/ (p # l /\ matchIndex[l][p] >= c) })
  /\ commitIndex' = [commitIndex EXCEPT ![l] = c]
  /\ UNCHANGED << state, currentTerm, votedFor, leaderId, log, lastApplied, lastAppliedTerm, electionTimeoutRand, requestTimeout, timeoutElapsed, nextIndex, matchIndex, snapshotLastIdx, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIdx, nextSnapshotLastTerm, votingCfgChangeLogIdx, nodes, pending, preVotes, votes, conflictDeleteIdx >>

PeriodicElectionTimeout(n) ==
  /\ n \in Node
  /\ state[n] # LEADER
  /\ timeoutElapsed[n] < electionTimeoutRand[n]
  /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![n] = timeoutElapsed[n] + 1]
  /\ UNCHANGED << state, currentTerm, votedFor, leaderId, log, commitIndex, lastApplied, lastAppliedTerm, electionTimeoutRand, requestTimeout, nextIndex, matchIndex, snapshotLastIdx, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIdx, nextSnapshotLastTerm, votingCfgChangeLogIdx, nodes, pending, preVotes, votes, conflictDeleteIdx >>

PeriodicHeartbeat(n) ==
  /\ n \in Node
  /\ state[n] = LEADER
  /\ timeoutElapsed[n] < requestTimeout[n]
  /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![n] = timeoutElapsed[n] + 1]
  /\ UNCHANGED << state, currentTerm, votedFor, leaderId, log, commitIndex, lastApplied, lastAppliedTerm, electionTimeoutRand, requestTimeout, nextIndex, matchIndex, snapshotLastIdx, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIdx, nextSnapshotLastTerm, votingCfgChangeLogIdx, nodes, pending, preVotes, votes, conflictDeleteIdx >>

AddNode(l, x) ==
  /\ l \in Node /\ x \in Node
  /\ state[l] = LEADER
  /\ votingCfgChangeLogIdx[l] = 0
  /\ nodes[x].active = FALSE \/ ~nodes[x].voting
  /\ LET e == Entry(currentTerm[l], ADD_NODE, x) IN
     LET newLog == [log EXCEPT ![l] = Append(log[l], e)] IN
     LET newLastIdx == snapshotLastIdx[l] + Len(newLog[l]) IN
     /\ log' = newLog
     /\ votingCfgChangeLogIdx' = [votingCfgChangeLogIdx EXCEPT ![l] = newLastIdx]
     /\ nodes' = [nodes EXCEPT ![x] = [nodes[x] EXCEPT !.active = TRUE, !.voting = TRUE]]
     /\ UNCHANGED << state, currentTerm, votedFor, leaderId, commitIndex, lastApplied, lastAppliedTerm, electionTimeoutRand, requestTimeout, timeoutElapsed, nextIndex, matchIndex, snapshotLastIdx, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIdx, nextSnapshotLastTerm, pending, preVotes, votes, conflictDeleteIdx >>

RemoveNode(l, x) ==
  /\ l \in Node /\ x \in Node
  /\ state[l] = LEADER
  /\ votingCfgChangeLogIdx[l] = 0
  /\ nodes[x].active
  /\ LET e == Entry(currentTerm[l], REMOVE_NODE, x) IN
     LET newLog == [log EXCEPT ![l] = Append(log[l], e)] IN
     LET newLastIdx == snapshotLastIdx[l] + Len(newLog[l]) IN
     /\ log' = newLog
     /\ votingCfgChangeLogIdx' = [votingCfgChangeLogIdx EXCEPT ![l] = newLastIdx]
     /\ nodes' = [nodes EXCEPT ![x] = [nodes[x] EXCEPT !.active = FALSE, !.voting = FALSE]]
     /\ UNCHANGED << state, currentTerm, votedFor, leaderId, commitIndex, lastApplied, lastAppliedTerm, electionTimeoutRand, requestTimeout, timeoutElapsed, nextIndex, matchIndex, snapshotLastIdx, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIdx, nextSnapshotLastTerm, pending, preVotes, votes, conflictDeleteIdx >>

SnapshotBegin(n) ==
  /\ n \in Node
  /\ ~snapshotInProgress[n]
  /\ commitIndex[n] = lastApplied[n]
  /\ lastApplied[n] > snapshotLastIdx[n]
  /\ snapshotInProgress' = [snapshotInProgress EXCEPT ![n] = TRUE]
  /\ nextSnapshotLastIdx' = [nextSnapshotLastIdx EXCEPT ![n] = lastApplied[n]]
  /\ nextSnapshotLastTerm' = [nextSnapshotLastTerm EXCEPT ![n] = lastAppliedTerm[n]]
  /\ UNCHANGED << state, currentTerm, votedFor, leaderId, log, commitIndex, lastApplied, lastAppliedTerm, electionTimeoutRand, requestTimeout, timeoutElapsed, nextIndex, matchIndex, snapshotLastIdx, snapshotLastTerm, votingCfgChangeLogIdx, nodes, pending, preVotes, votes, conflictDeleteIdx >>

SnapshotEnd(n) ==
  /\ n \in Node
  /\ snapshotInProgress[n]
  /\ nextSnapshotLastIdx[n] >= snapshotLastIdx[n]
  /\ LET k == nextSnapshotLastIdx[n] - snapshotLastIdx[n] IN
     /\ snapshotLastIdx' = [snapshotLastIdx EXCEPT ![n] = nextSnapshotLastIdx[n]]
     /\ snapshotLastTerm' = [snapshotLastTerm EXCEPT ![n] = nextSnapshotLastTerm[n]]
     /\ log' = [log EXCEPT ![n] = SubSeq(log[n], k + 1, Len(log[n]))]
     /\ snapshotInProgress' = [snapshotInProgress EXCEPT ![n] = FALSE]
     /\ UNCHANGED << state, currentTerm, votedFor, leaderId, commitIndex, lastApplied, lastAppliedTerm, electionTimeoutRand, requestTimeout, timeoutElapsed, nextIndex, matchIndex, nextSnapshotLastIdx, nextSnapshotLastTerm, votingCfgChangeLogIdx, nodes, pending, preVotes, votes, conflictDeleteIdx >>

ApplyConfigChange(n) ==
  /\ n \in Node
  /\ lastApplied[n] < commitIndex[n]
  /\ LET idx == lastApplied[n] + 1 IN
     LET isSnapBase == (idx = snapshotLastIdx[n]) IN
     LET e == IF isSnapBase THEN Entry(snapshotLastTerm[n], NO_OP, NoNode) ELSE log[n][idx - snapshotLastIdx[n]] IN
     /\ lastApplied' = [lastApplied EXCEPT ![n] = idx]
     /\ lastAppliedTerm' = [lastAppliedTerm EXCEPT ![n] = e.term]
     /\ votingCfgChangeLogIdx' = [votingCfgChangeLogIdx EXCEPT ![n] = IF votingCfgChangeLogIdx[n] = idx THEN 0 ELSE votingCfgChangeLogIdx[n]]
     /\ IF e.type = ADD_NODE THEN
          /\ nodes' = [nodes EXCEPT ![e.node] = [nodes[e.node] EXCEPT !.additionCommitted = TRUE, !.votingCommitted = TRUE, !.hasSufficientLogs = TRUE, !.active = TRUE, !.voting = TRUE]]
          /\ UNCHANGED << state, currentTerm, votedFor, leaderId, log, commitIndex, electionTimeoutRand, requestTimeout, timeoutElapsed, nextIndex, matchIndex, snapshotLastIdx, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIdx, nextSnapshotLastTerm, pending, preVotes, votes, conflictDeleteIdx >>
        ELSE IF e.type = ADD_NONVOTING_NODE THEN
          /\ nodes' = [nodes EXCEPT ![e.node] = [nodes[e.node] EXCEPT !.additionCommitted = TRUE, !.active = TRUE, !.voting = FALSE]]
          /\ UNCHANGED << state, currentTerm, votedFor, leaderId, log, commitIndex, electionTimeoutRand, requestTimeout, timeoutElapsed, nextIndex, matchIndex, snapshotLastIdx, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIdx, nextSnapshotLastTerm, pending, preVotes, votes, conflictDeleteIdx >>
        ELSE IF e.type = REMOVE_NODE THEN
          /\ nodes' = [nodes EXCEPT ![e.node] = [nodes[e.node] EXCEPT !.active = FALSE, !.voting = FALSE]]
          /\ UNCHANGED << state, currentTerm, votedFor, leaderId, log, commitIndex, electionTimeoutRand, requestTimeout, timeoutElapsed, nextIndex, matchIndex, snapshotLastIdx, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIdx, nextSnapshotLastTerm, pending, preVotes, votes, conflictDeleteIdx >>
        ELSE
          /\ UNCHANGED << state, currentTerm, votedFor, leaderId, log, commitIndex, electionTimeoutRand, requestTimeout, timeoutElapsed, nextIndex, matchIndex, snapshotLastIdx, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIdx, nextSnapshotLastTerm, pending, preVotes, votes, nodes, conflictDeleteIdx >>

Next ==
  \/ \E n \in Node : BecomeFollower(n)
  \/ \E n \in Node : BecomePreCandidate(n)
  \/ \E n \in Node : BecomeCandidate(n)
  \/ \E n \in Node : BecomeLeader(n)
  \/ RecvRequestVote
  \/ RecvRequestVoteResponse
  \/ RecvAppendEntries
  \/ RecvAppendEntriesResponse
  \/ \E l,f \in Node, k \in Nat : SendAppendEntries(l, f, k)
  \/ \E l,f \in Node : SendHeartbeat(l, f)
  \/ \E n \in Node : ElectionStart(n)
  \/ \E n \in Node : ElectionTimeout(n)
  \/ \E l \in Node : LogAppend(l)
  \/ \E n \in Node : LogDelete(n)
  \/ \E l \in Node, c \in Nat : LogCommit(l, c)
  \/ \E n \in Node : PeriodicElectionTimeout(n)
  \/ \E n \in Node : PeriodicHeartbeat(n)
  \/ \E l,x \in Node : AddNode(l, x)
  \/ \E l,x \in Node : RemoveNode(l, x)
  \/ \E n \in Node : SnapshotBegin(n)
  \/ \E n \in Node : SnapshotEnd(n)
  \/ \E n \in Node : ApplyConfigChange(n)
  \/ \E c,p \in Node : SendRequestVote(c, p)

Spec == Init /\ [][Next]_vars

====