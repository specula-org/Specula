---- MODULE redisraft ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Node, NoNode, ETimeoutMin, RTimeout

VARIABLES
  Voters,
  state,
  currentTerm,
  votedFor,
  log,
  commitIndex,
  lastApplied,
  leaderId,
  nextIndex,
  matchIndex,
  electionElapsed,
  electionTimeout,
  requestElapsed,
  requestTimeout,
  snapshotLastIdx,
  snapshotLastTerm,
  snapshotInProgress,
  grantedPrevotes,
  grantedVotes,
  Net

EntryType == {"NOOP","DATA","ADD_NODE","REMOVE_NODE"}

Entry(e) ==
  /\ e \in [term: Nat, type: EntryType, node: Node \cup {NoNode}]

Max(a, b) == IF a < b THEN b ELSE a
Min(a, b) == IF a < b THEN a ELSE b

Index(n) == snapshotLastIdx[n] + Len(log[n])

TermAt(n, i) ==
  IF i = snapshotLastIdx[n] THEN snapshotLastTerm[n]
  ELSE IF snapshotLastIdx[n] < i /\ i <= snapshotLastIdx[n] + Len(log[n]) THEN
    log[n][i - snapshotLastIdx[n]].term
  ELSE 0

EntryAt(n, i) ==
  IF snapshotLastIdx[n] < i /\ i <= snapshotLastIdx[n] + Len(log[n]) THEN
    log[n][i - snapshotLastIdx[n]]
  ELSE
    [term |-> snapshotLastTerm[n], type |-> "NOOP", node |-> NoNode]

UpToDate(c, s) ==
  /\ TermAt(c, Index(c)) > TermAt(s, Index(s))
  \/ /\ TermAt(c, Index(c)) = TermAt(s, Index(s))
     /\ Index(c) >= Index(s)

Majority(S) == 2 * Cardinality(S) > 2 * Cardinality(Voters)

RandTimeout(t) == ETimeoutMin <= t /\ t < 2 * ETimeoutMin

MsgAppendReq(m) ==
  /\ m.type = "AppendEntries"
  /\ m.from \in Node /\ m.to \in Node
  /\ m.term \in Nat
  /\ m.leader \in Node
  /\ m.prevLogIndex \in Nat
  /\ m.prevLogTerm \in Nat
  /\ m.leaderCommit \in Nat
  /\ m.entries \in Seq([term: Nat, type: EntryType, node: Node \cup {NoNode}])

MsgAppendResp(m) ==
  /\ m.type = "AppendEntriesResp"
  /\ m.from \in Node /\ m.to \in Node
  /\ m.term \in Nat
  /\ m.success \in BOOLEAN
  /\ m.currentIdx \in Nat

MsgRVReq(m) ==
  /\ m.type = "RequestVote"
  /\ m.from \in Node /\ m.to \in Node
  /\ m.prevote \in BOOLEAN
  /\ m.term \in Nat
  /\ m.lastLogIndex \in Nat
  /\ m.lastLogTerm \in Nat
  /\ m.candidate \in Node

MsgRVResp(m) ==
  /\ m.type = "RequestVoteResp"
  /\ m.from \in Node /\ m.to \in Node
  /\ m.prevote \in BOOLEAN
  /\ m.requestTerm \in Nat
  /\ m.term \in Nat
  /\ m.voteGranted \in BOOLEAN

Message(m) == MsgAppendReq(m) \/ MsgAppendResp(m) \/ MsgRVReq(m) \/ MsgRVResp(m)

LastIndexLE(n, i) == i <= Index(n)

CanGrantVote(self, m) ==
  /\ m.term = currentTerm[self]
  /\ votedFor[self] \in {NoNode, m.candidate}
  /\ UpToDate(m.candidate, self)

RandomizeElectionTimeout(self) ==
  \E t \in Nat:
    /\ RandTimeout(t)
    /\ electionTimeout' = [electionTimeout EXCEPT ![self] = t]
    /\ UNCHANGED << Voters, state, currentTerm, votedFor, log, commitIndex, lastApplied, leaderId,
                    nextIndex, matchIndex, electionElapsed, requestElapsed, requestTimeout,
                    snapshotLastIdx, snapshotLastTerm, snapshotInProgress, grantedPrevotes, grantedVotes, Net >>

BecomeFollower(self) ==
  /\ state' = [state EXCEPT ![self] = "FOLLOWER"]
  /\ leaderId' = [leaderId EXCEPT ![self] = NoNode]
  /\ electionElapsed' = [electionElapsed EXCEPT ![self] = 0]
  /\ \E t \in Nat: RandTimeout(t) /\ electionTimeout' = [electionTimeout EXCEPT ![self] = t]
  /\ UNCHANGED << Voters, currentTerm, votedFor, log, commitIndex, lastApplied,
                  nextIndex, matchIndex, requestElapsed, requestTimeout,
                  snapshotLastIdx, snapshotLastTerm, snapshotInProgress, grantedPrevotes, grantedVotes, Net >>

BecomePreCandidate(self) ==
  /\ state[self] # "LEADER"
  /\ state' = [state EXCEPT ![self] = "PRECANDIDATE"]
  /\ grantedPrevotes' = [grantedPrevotes EXCEPT ![self] = {}]
  /\ grantedVotes' = [grantedVotes EXCEPT ![self] = {}]
  /\ \E msgs \in SUBSET { [ type |-> "RequestVote",
                           from |-> self, to |-> dest, prevote |-> TRUE,
                           term |-> currentTerm[self] + 1,
                           lastLogIndex |-> Index(self),
                           lastLogTerm |-> TermAt(self, Index(self)),
                           candidate |-> self ]
                         : dest \in Voters /\ dest # self }:
       /\ Net' = Net \cup msgs
  /\ UNCHANGED << Voters, currentTerm, votedFor, log, commitIndex, lastApplied, leaderId,
                  nextIndex, matchIndex, electionElapsed, electionTimeout, requestElapsed, requestTimeout,
                  snapshotLastIdx, snapshotLastTerm, snapshotInProgress >>

BecomeCandidate(self) ==
  /\ state[self] \in {"FOLLOWER","PRECANDIDATE","CANDIDATE"}
  /\ currentTerm' = [currentTerm EXCEPT ![self] = @ + 1]
  /\ votedFor' = [votedFor EXCEPT ![self] = self]
  /\ state' = [state EXCEPT ![self] = "CANDIDATE"]
  /\ leaderId' = [leaderId EXCEPT ![self] = NoNode]
  /\ electionElapsed' = [electionElapsed EXCEPT ![self] = 0]
  /\ \E t \in Nat: RandTimeout(t) /\ electionTimeout' = [electionTimeout EXCEPT ![self] = t]
  /\ grantedVotes' = [grantedVotes EXCEPT ![self] = {self}]
  /\ grantedPrevotes' = [grantedPrevotes EXCEPT ![self] = {}]
  /\ \E msgs \in SUBSET { [ type |-> "RequestVote",
                           from |-> self, to |-> dest, prevote |-> FALSE,
                           term |-> currentTerm'[self],
                           lastLogIndex |-> Index(self),
                           lastLogTerm |-> TermAt(self, Index(self)),
                           candidate |-> self ]
                         : dest \in Voters /\ dest # self }:
       /\ Net' = Net \cup msgs
  /\ UNCHANGED << Voters, log, commitIndex, lastApplied,
                  nextIndex, matchIndex, requestElapsed, requestTimeout,
                  snapshotLastIdx, snapshotLastTerm, snapshotInProgress >>

BecomeLeader(self) ==
  /\ state[self] = "CANDIDATE"
  /\ Majority(grantedVotes[self] \cap Voters)
  /\ state' = [state EXCEPT ![self] = "LEADER"]
  /\ leaderId' = [leaderId EXCEPT ![self] = self]
  /\ requestElapsed' = [requestElapsed EXCEPT ![self] = 0]
  /\ log' = [log EXCEPT ![self] = @ \o << [term |-> currentTerm[self], type |-> "NOOP", node |-> NoNode] >>]
  /\ commitIndex' = commitIndex
  /\ nextIndex' =
      [i \in Node |-> [j \in Node |-> IF i = self /\ j # self THEN Index(self) + 1 ELSE nextIndex[i][j]]]
  /\ matchIndex' =
      [i \in Node |-> [j \in Node |-> IF i = self /\ j = self THEN Index(self) ELSE matchIndex[i][j]]]
  /\ UNCHANGED << Voters, currentTerm, votedFor, electionElapsed, electionTimeout, requestTimeout,
                  snapshotLastIdx, snapshotLastTerm, snapshotInProgress, grantedPrevotes, grantedVotes, Net >>

ElectionStartPreCandidate(self) ==
  /\ state[self] # "LEADER"
  /\ electionElapsed[self] >= electionTimeout[self]
  /\ electionElapsed' = [electionElapsed EXCEPT ![self] = 0]
  /\ \E t \in Nat: RandTimeout(t) /\ electionTimeout' = [electionTimeout EXCEPT ![self] = t]
  /\ state' = [state EXCEPT ![self] = "PRECANDIDATE"]
  /\ grantedPrevotes' = [grantedPrevotes EXCEPT ![self] = {}]
  /\ grantedVotes' = [grantedVotes EXCEPT ![self] = {}]
  /\ \E msgs \in SUBSET { [ type |-> "RequestVote",
                           from |-> self, to |-> dest, prevote |-> TRUE,
                           term |-> currentTerm[self] + 1,
                           lastLogIndex |-> Index(self),
                           lastLogTerm |-> TermAt(self, Index(self)),
                           candidate |-> self ]
                         : dest \in Voters /\ dest # self }:
       /\ Net' = Net \cup msgs
  /\ UNCHANGED << Voters, currentTerm, votedFor, log, commitIndex, lastApplied, leaderId,
                  nextIndex, matchIndex, requestElapsed, requestTimeout,
                  snapshotLastIdx, snapshotLastTerm, snapshotInProgress >>

ElectionStartCandidate(self) ==
  /\ state[self] # "LEADER"
  /\ electionElapsed[self] >= electionTimeout[self]
  /\ currentTerm' = [currentTerm EXCEPT ![self] = @ + 1]
  /\ votedFor' = [votedFor EXCEPT ![self] = self]
  /\ state' = [state EXCEPT ![self] = "CANDIDATE"]
  /\ leaderId' = [leaderId EXCEPT ![self] = NoNode]
  /\ electionElapsed' = [electionElapsed EXCEPT ![self] = 0]
  /\ \E t \in Nat: RandTimeout(t) /\ electionTimeout' = [electionTimeout EXCEPT ![self] = t]
  /\ grantedVotes' = [grantedVotes EXCEPT ![self] = {self}]
  /\ grantedPrevotes' = [grantedPrevotes EXCEPT ![self] = {}]
  /\ \E msgs \in SUBSET { [ type |-> "RequestVote",
                           from |-> self, to |-> dest, prevote |-> FALSE,
                           term |-> currentTerm'[self],
                           lastLogIndex |-> Index(self),
                           lastLogTerm |-> TermAt(self, Index(self)),
                           candidate |-> self ]
                         : dest \in Voters /\ dest # self }:
       /\ Net' = Net \cup msgs
  /\ UNCHANGED << Voters, log, commitIndex, lastApplied,
                  nextIndex, matchIndex, requestElapsed, requestTimeout,
                  snapshotLastIdx, snapshotLastTerm, snapshotInProgress >>

ElectionStart(self) ==
  ElectionStartPreCandidate(self) \/ ElectionStartCandidate(self)

ElectionTimeout(self) ==
  /\ state[self] # "LEADER"
  /\ electionElapsed[self] < electionTimeout[self]
  /\ electionElapsed' = [electionElapsed EXCEPT ![self] = @ + 1]
  /\ UNCHANGED << Voters, state, currentTerm, votedFor, log, commitIndex, lastApplied, leaderId,
                  nextIndex, matchIndex, electionTimeout, requestElapsed, requestTimeout,
                  snapshotLastIdx, snapshotLastTerm, snapshotInProgress, grantedPrevotes, grantedVotes, Net >>

PeriodicElectionTimeout(self) == ElectionTimeout(self)

PeriodicHeartbeat(self) ==
  /\ state[self] = "LEADER"
  /\ requestElapsed' = [requestElapsed EXCEPT ![self] = @ + 1]
  /\ UNCHANGED << Voters, state, currentTerm, votedFor, log, commitIndex, lastApplied, leaderId,
                  nextIndex, matchIndex, electionElapsed, electionTimeout, requestTimeout,
                  snapshotLastIdx, snapshotLastTerm, snapshotInProgress, grantedPrevotes, grantedVotes, Net >>

SendAppendEntries(leader, follower) ==
  /\ state[leader] = "LEADER"
  /\ follower \in Voters /\ follower # leader
  /\ nextIndex[leader][follower] >= snapshotLastIdx[leader] + 1
  /\ nextIndex[leader][follower] <= Index(leader) + 1
  /\ \E ent \in Seq([term: Nat, type: EntryType, node: Node \cup {NoNode}]):
       /\ ent = SubSeq(log[leader],
                       Max(1, nextIndex[leader][follower] - snapshotLastIdx[leader]),
                       Len(log[leader]))
       /\ Net' = Net \cup {
            [ type |-> "AppendEntries",
              from |-> leader, to |-> follower,
              term |-> currentTerm[leader], leader |-> leader,
              prevLogIndex |-> nextIndex[leader][follower] - 1,
              prevLogTerm |-> TermAt(leader, nextIndex[leader][follower] - 1),
              leaderCommit |-> commitIndex[leader],
              entries |-> ent ] }
  /\ UNCHANGED << Voters, state, currentTerm, votedFor, log, commitIndex, lastApplied, leaderId,
                  nextIndex, matchIndex, electionElapsed, electionTimeout, requestElapsed, requestTimeout,
                  snapshotLastIdx, snapshotLastTerm, snapshotInProgress, grantedPrevotes, grantedVotes >>

SendHeartbeat(leader, follower) ==
  /\ state[leader] = "LEADER"
  /\ follower \in Voters /\ follower # leader
  /\ Net' = Net \cup {
        [ type |-> "AppendEntries",
          from |-> leader, to |-> follower,
          term |-> currentTerm[leader], leader |-> leader,
          prevLogIndex |-> nextIndex[leader][follower] - 1,
          prevLogTerm |-> TermAt(leader, nextIndex[leader][follower] - 1),
          leaderCommit |-> commitIndex[leader],
          entries |-> << >> ] }
  /\ requestElapsed' = [requestElapsed EXCEPT ![leader] = 0]
  /\ UNCHANGED << Voters, state, currentTerm, votedFor, log, commitIndex, lastApplied, leaderId,
                  nextIndex, matchIndex, electionElapsed, electionTimeout, requestTimeout,
                  snapshotLastIdx, snapshotLastTerm, snapshotInProgress, grantedPrevotes, grantedVotes >>

RecvAppendEntries(self) ==
  \E m \in Net:
    /\ MsgAppendReq(m) /\ m.to = self
    /\ LET Net1 == Net \ {m} IN
       IF m.term < currentTerm[self] THEN
         /\ Net' = Net1 \cup {
              [ type |-> "AppendEntriesResp",
                from |-> self, to |-> m.from,
                term |-> currentTerm[self], success |-> FALSE,
                currentIdx |-> Index(self) ] }
         /\ UNCHANGED << Voters, state, currentTerm, votedFor, log, commitIndex, lastApplied, leaderId,
                         nextIndex, matchIndex, electionElapsed, electionTimeout, requestElapsed, requestTimeout,
                         snapshotLastIdx, snapshotLastTerm, snapshotInProgress, grantedPrevotes, grantedVotes >>
       ELSE
         /\ currentTerm' = [currentTerm EXCEPT ![self] = m.term]
         /\ leaderId' = [leaderId EXCEPT ![self] = m.leader]
         /\ state' = [state EXCEPT ![self] = "FOLLOWER" ]
         /\ electionElapsed' = [electionElapsed EXCEPT ![self] = 0]
         /\ votedFor' = votedFor
         /\ grantedPrevotes' = grantedPrevotes
         /\ grantedVotes' = grantedVotes
         /\ (* Fix: Wrap local definition AppendOK in LET-IN to avoid illegal '==' in conjunction *)
            LET AppendOK ==
              IF m.prevLogIndex = snapshotLastIdx[self] THEN m.prevLogTerm = snapshotLastTerm[self]
              ELSE /\ snapshotLastIdx[self] < m.prevLogIndex
                   /\ m.prevLogIndex <= Index(self)
                   /\ TermAt(self, m.prevLogIndex) = m.prevLogTerm
            IN
              IF ~AppendOK THEN
                /\ log' =
                     [log EXCEPT ![self] =
                       SubSeq(log[self], 1, Max(0, m.prevLogIndex - snapshotLastIdx[self])) ]
                /\ commitIndex' = commitIndex
                /\ lastApplied' = lastApplied
                /\ snapshotLastIdx' = snapshotLastIdx
                /\ snapshotLastTerm' = snapshotLastTerm
                /\ snapshotInProgress' = snapshotInProgress
                /\ Net' = Net1 \cup {
                     [ type |-> "AppendEntriesResp",
                       from |-> self, to |-> m.from,
                       term |-> currentTerm'[self], success |-> FALSE,
                       currentIdx |-> Index(self) ] }
                /\ UNCHANGED << Voters, nextIndex, matchIndex, electionTimeout, requestElapsed, requestTimeout >>
              ELSE
                /\ LET cut == m.prevLogIndex - snapshotLastIdx[self] IN
                   log' =
                     [log EXCEPT ![self] =
                        SubSeq(log[self], 1, cut) \o m.entries]
                /\ commitIndex' = [commitIndex EXCEPT ![self] = Min(m.leaderCommit, Index(self))]
                /\ lastApplied' = lastApplied
                /\ snapshotLastIdx' = snapshotLastIdx
                /\ snapshotLastTerm' = snapshotLastTerm
                /\ snapshotInProgress' = snapshotInProgress
                /\ Net' = Net1 \cup {
                     [ type |-> "AppendEntriesResp",
                       from |-> self, to |-> m.from,
                       term |-> currentTerm'[self], success |-> TRUE,
                       currentIdx |-> Index(self) ] }
                /\ UNCHANGED << Voters, nextIndex, matchIndex, electionTimeout, requestElapsed, requestTimeout >>

RecvAppendEntriesResponse(leader) ==
  \E m \in Net:
    /\ MsgAppendResp(m) /\ m.to = leader
    /\ LET Net1 == Net \ {m} IN
       IF m.term > currentTerm[leader] THEN
         /\ currentTerm' = [currentTerm EXCEPT ![leader] = m.term]
         /\ votedFor' = [votedFor EXCEPT ![leader] = NoNode]
         /\ state' = [state EXCEPT ![leader] = "FOLLOWER"]
         /\ leaderId' = [leaderId EXCEPT ![leader] = NoNode]
         /\ Net' = Net1
         /\ UNCHANGED << Voters, log, commitIndex, lastApplied, nextIndex, matchIndex,
                         electionElapsed, electionTimeout, requestElapsed, requestTimeout,
                         snapshotLastIdx, snapshotLastTerm, snapshotInProgress, grantedPrevotes, grantedVotes >>
       ELSE
         /\ IF m.success THEN
              /\ matchIndex' =
                   [matchIndex EXCEPT ![leader] =
                      [matchIndex[leader] EXCEPT ![m.from] = Max(@, m.currentIdx)]]
              /\ nextIndex' =
                   [nextIndex EXCEPT ![leader] =
                      [nextIndex[leader] EXCEPT ![m.from] = Max(@, m.currentIdx + 1)]]
            ELSE
              /\ matchIndex' = matchIndex
              /\ nextIndex' =
                   [nextIndex EXCEPT ![leader] =
                      [nextIndex[leader] EXCEPT ![m.from] = Max(1, Min(@ - 1, m.currentIdx + 1))]]
         /\ Net' = Net1
         /\ UNCHANGED << Voters, state, currentTerm, votedFor, log, commitIndex, lastApplied, leaderId,
                         electionElapsed, electionTimeout, requestElapsed, requestTimeout,
                         snapshotLastIdx, snapshotLastTerm, snapshotInProgress, grantedPrevotes, grantedVotes >>

RecvRequestVote(self) ==
  \E m \in Net:
    /\ MsgRVReq(m) /\ m.to = self
    /\ LET Net1 == Net \ {m} IN
       IF m.prevote THEN
         /\ IF /\ leaderId[self] # NoNode /\ electionElapsed[self] < electionTimeout[self] THEN
              /\ Net' = Net1 \cup {
                   [ type |-> "RequestVoteResp",
                     from |-> self, to |-> m.from,
                     prevote |-> TRUE, requestTerm |-> m.term,
                     term |-> currentTerm[self], voteGranted |-> FALSE ] }
              /\ UNCHANGED << Voters, state, currentTerm, votedFor, log, commitIndex, lastApplied, leaderId,
                              nextIndex, matchIndex, electionElapsed, electionTimeout, requestElapsed, requestTimeout,
                              snapshotLastIdx, snapshotLastTerm, snapshotInProgress, grantedPrevotes, grantedVotes >>
            ELSE
              /\ Net' = Net1 \cup {
                   [ type |-> "RequestVoteResp",
                     from |-> self, to |-> m.from,
                     prevote |-> TRUE, requestTerm |-> m.term,
                     term |-> currentTerm[self],
                     voteGranted |-> UpToDate(m.candidate, self) ] }
              /\ UNCHANGED << Voters, state, currentTerm, votedFor, log, commitIndex, lastApplied, leaderId,
                              nextIndex, matchIndex, electionElapsed, electionTimeout, requestElapsed, requestTimeout,
                              snapshotLastIdx, snapshotLastTerm, snapshotInProgress, grantedPrevotes, grantedVotes >>
       ELSE
         /\ (* Fix: Replace illegal inline '==' and undeclared temporaries with a LET-IN block *)
            LET currentTerm1 ==
                  IF m.term > currentTerm[self]
                    THEN [currentTerm EXCEPT ![self] = m.term]
                    ELSE currentTerm
                votedFor1 ==
                  IF m.term > currentTerm[self]
                    THEN [votedFor EXCEPT ![self] = NoNode]
                    ELSE votedFor
                state1 ==
                  IF m.term > currentTerm[self]
                    THEN [state EXCEPT ![self] = "FOLLOWER"]
                    ELSE state
                leaderId1 ==
                  IF m.term > currentTerm[self]
                    THEN [leaderId EXCEPT ![self] = NoNode]
                    ELSE leaderId
                grant ==
                  (m.term = currentTerm1[self])
                  /\ UpToDate(m.candidate, self)
                  /\ (votedFor1[self] \in {NoNode, m.candidate})
            IN
              /\ votedFor' = IF grant THEN [votedFor1 EXCEPT ![self] = m.candidate] ELSE votedFor1
              /\ currentTerm' = currentTerm1
              /\ state' = state1
              /\ leaderId' = leaderId1
              /\ electionElapsed' = [electionElapsed EXCEPT ![self] = IF grant THEN 0 ELSE @]
              /\ Net' = Net1 \cup {
                   [ type |-> "RequestVoteResp",
                     from |-> self, to |-> m.from,
                     prevote |-> FALSE, requestTerm |-> m.term,
                     term |-> currentTerm'[self], voteGranted |-> grant ] }
              /\ UNCHANGED << Voters, log, commitIndex, lastApplied,
                              nextIndex, matchIndex, electionTimeout, requestElapsed, requestTimeout,
                              snapshotLastIdx, snapshotLastTerm, snapshotInProgress, grantedPrevotes, grantedVotes >>

RecvRequestVoteResponse(self) ==
  \E m \in Net:
    /\ MsgRVResp(m) /\ m.to = self
    /\ LET Net1 == Net \ {m} IN
       IF m.term > currentTerm[self] THEN
         /\ currentTerm' = [currentTerm EXCEPT ![self] = m.term]
         /\ votedFor' = [votedFor EXCEPT ![self] = NoNode]
         /\ state' = [state EXCEPT ![self] = "FOLLOWER"]
         /\ leaderId' = [leaderId EXCEPT ![self] = NoNode]
         /\ Net' = Net1
         /\ UNCHANGED << Voters, log, commitIndex, lastApplied, nextIndex, matchIndex,
                         electionElapsed, electionTimeout, requestElapsed, requestTimeout,
                         snapshotLastIdx, snapshotLastTerm, snapshotInProgress, grantedPrevotes, grantedVotes >>
       ELSE
         /\ IF m.prevote THEN
              /\ /\ state[self] = "PRECANDIDATE"
                 /\ m.requestTerm = currentTerm[self] + 1
              /\ grantedPrevotes' =
                   [grantedPrevotes EXCEPT ![self] =
                      IF m.voteGranted /\ m.from \in Voters THEN @ \cup {m.from} ELSE @]
              /\ grantedVotes' = grantedVotes
              /\ state' = state
              /\ currentTerm' = currentTerm
              /\ votedFor' = votedFor
              /\ leaderId' = leaderId
              /\ Net' = Net1
              /\ UNCHANGED << Voters, log, commitIndex, lastApplied, nextIndex, matchIndex,
                              electionElapsed, electionTimeout, requestElapsed, requestTimeout,
                              snapshotLastIdx, snapshotLastTerm, snapshotInProgress >>
            ELSE
              /\ /\ state[self] = "CANDIDATE"
                 /\ m.requestTerm = currentTerm[self]
              /\ grantedVotes' =
                   [grantedVotes EXCEPT ![self] =
                      IF m.voteGranted /\ m.from \in Voters THEN @ \cup {m.from} ELSE @]
              /\ grantedPrevotes' = grantedPrevotes
              /\ state' = state
              /\ currentTerm' = currentTerm
              /\ votedFor' = votedFor
              /\ leaderId' = leaderId
              /\ Net' = Net1
              /\ UNCHANGED << Voters, log, commitIndex, lastApplied, nextIndex, matchIndex,
                              electionElapsed, electionTimeout, requestElapsed, requestTimeout,
                              snapshotLastIdx, snapshotLastTerm, snapshotInProgress >>

LogAppend(leader, etype, nodeid) ==
  /\ state[leader] = "LEADER"
  /\ etype \in {"DATA","ADD_NODE","REMOVE_NODE"}
  /\ nodeid \in Node \cup {NoNode}
  /\ log' = [log EXCEPT ![leader] = @ \o << [term |-> currentTerm[leader], type |-> etype, node |-> nodeid] >>]
  /\ UNCHANGED << Voters, state, currentTerm, votedFor, commitIndex, lastApplied, leaderId,
                  nextIndex, matchIndex, electionElapsed, electionTimeout, requestElapsed, requestTimeout,
                  snapshotLastIdx, snapshotLastTerm, snapshotInProgress, grantedPrevotes, grantedVotes, Net >>

LogDelete(self, idx) ==
  /\ snapshotLastIdx[self] < idx /\ idx <= Index(self)
  /\ log' = [log EXCEPT ![self] = SubSeq(log[self], 1, idx - snapshotLastIdx[self] - 1)]
  /\ UNCHANGED << Voters, state, currentTerm, votedFor, commitIndex, lastApplied, leaderId,
                  nextIndex, matchIndex, electionElapsed, electionTimeout, requestElapsed, requestTimeout,
                  snapshotLastIdx, snapshotLastTerm, snapshotInProgress, grantedPrevotes, grantedVotes, Net >>

LogCommit(leader) ==
  /\ state[leader] = "LEADER"
  /\ LET idxs ==
        { IF n = leader THEN Index(leader) ELSE matchIndex[leader][n] : n \in Voters }
     IN /\ idxs # {}
        /\ \E newc \in Nat:
             /\ newc \in idxs
             /\ newc > commitIndex[leader]
             /\ TermAt(leader, newc) = currentTerm[leader]
             /\ Cardinality({ i \in Voters : (IF i = leader THEN Index(leader) ELSE matchIndex[leader][i]) >= newc }) > Cardinality(Voters) \div 2
             /\ commitIndex' = [commitIndex EXCEPT ![leader] = newc]
  /\ UNCHANGED << Voters, state, currentTerm, votedFor, log, lastApplied, leaderId,
                  nextIndex, matchIndex, electionElapsed, electionTimeout, requestElapsed, requestTimeout,
                  snapshotLastIdx, snapshotLastTerm, snapshotInProgress, grantedPrevotes, grantedVotes, Net >>

LogCommitFollower(self) ==
  /\ state[self] # "LEADER"
  /\ lastApplied[self] < commitIndex[self]
  /\ \E i \in Nat:
       /\ i = lastApplied[self] + 1
       /\ i <= commitIndex[self]
       /\ lastApplied' = [lastApplied EXCEPT ![self] = i]
       /\ UNCHANGED << Voters, state, currentTerm, votedFor, log, commitIndex, leaderId,
                       nextIndex, matchIndex, electionElapsed, electionTimeout, requestElapsed, requestTimeout,
                       snapshotLastIdx, snapshotLastTerm, snapshotInProgress, grantedPrevotes, grantedVotes, Net >>

ApplyConfigChange(self) ==
  /\ lastApplied[self] < commitIndex[self]
  /\ \E i \in Nat:
       /\ i = lastApplied[self] + 1
       /\ i <= commitIndex[self]
       /\ LET e == EntryAt(self, i) IN
          /\ e.type \in {"ADD_NODE","REMOVE_NODE"}
          /\ Voters' = IF e.type = "ADD_NODE" THEN Voters \cup {e.node} ELSE Voters \ {e.node}
          /\ lastApplied' = [lastApplied EXCEPT ![self] = i]
          /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, leaderId,
                          nextIndex, matchIndex, electionElapsed, electionTimeout, requestElapsed, requestTimeout,
                          snapshotLastIdx, snapshotLastTerm, snapshotInProgress, grantedPrevotes, grantedVotes, Net >>

AddNode(leader, nodeid) ==
  /\ state[leader] = "LEADER"
  /\ nodeid \in Node
  /\ nodeid \notin Voters
  /\ LogAppend(leader, "ADD_NODE", nodeid)

RemoveNode(leader, nodeid) ==
  /\ state[leader] = "LEADER"
  /\ nodeid \in Voters
  /\ LogAppend(leader, "REMOVE_NODE", nodeid)

SnapshotBegin(self) ==
  /\ ~snapshotInProgress[self]
  /\ commitIndex[self] > snapshotLastIdx[self]
  /\ snapshotInProgress' = [snapshotInProgress EXCEPT ![self] = TRUE]
  /\ UNCHANGED << Voters, state, currentTerm, votedFor, log, commitIndex, lastApplied, leaderId,
                  nextIndex, matchIndex, electionElapsed, electionTimeout, requestElapsed, requestTimeout,
                  snapshotLastIdx, snapshotLastTerm, grantedPrevotes, grantedVotes, Net >>

SnapshotEnd(self) ==
  /\ snapshotInProgress[self]
  /\ lastApplied[self] >= snapshotLastIdx[self]
  /\ snapshotLastIdx' = [snapshotLastIdx EXCEPT ![self] = lastApplied[self]]
  /\ snapshotLastTerm' = [snapshotLastTerm EXCEPT ![self] = TermAt(self, lastApplied[self])]
  /\ log' =
      [log EXCEPT ![self] =
         SubSeq(log[self],
                Max(1, snapshotLastIdx'[self] - snapshotLastIdx[self] + 1),
                Len(log[self]))]
  /\ snapshotInProgress' = [snapshotInProgress EXCEPT ![self] = FALSE]
  /\ UNCHANGED << Voters, state, currentTerm, votedFor, commitIndex, lastApplied, leaderId,
                  nextIndex, matchIndex, electionElapsed, electionTimeout, requestElapsed, requestTimeout,
                  grantedPrevotes, grantedVotes, Net >>

TermAdvanceOnHigherTerm(self) ==
  \E m \in Net:
    /\ m.to = self
    /\ Message(m)
    /\ m.term > currentTerm[self]
    /\ currentTerm' = [currentTerm EXCEPT ![self] = m.term]
    /\ votedFor' = [votedFor EXCEPT ![self] = NoNode]
    /\ state' = [state EXCEPT ![self] = "FOLLOWER"]
    /\ leaderId' = [leaderId EXCEPT ![self] = NoNode]
    /\ UNCHANGED << Voters, log, commitIndex, lastApplied, nextIndex, matchIndex,
                    electionElapsed, electionTimeout, requestElapsed, requestTimeout,
                    snapshotLastIdx, snapshotLastTerm, snapshotInProgress, grantedPrevotes, grantedVotes, Net >>

Init ==
  /\ Voters \subseteq Node /\ Voters # {}
  /\ state \in [Node -> {"FOLLOWER","PRECANDIDATE","CANDIDATE","LEADER"}]
  /\ \A n \in Node: state[n] = "FOLLOWER"
  /\ currentTerm \in [Node -> Nat] /\ \A n \in Node: currentTerm[n] = 0
  /\ votedFor \in [Node -> (Node \cup {NoNode})] /\ \A n \in Node: votedFor[n] = NoNode
  /\ log \in [Node -> Seq([term: Nat, type: EntryType, node: Node \cup {NoNode}])]
  /\ \A n \in Node: log[n] = << >>
  /\ commitIndex \in [Node -> Nat] /\ \A n \in Node: commitIndex[n] = 0
  /\ lastApplied \in [Node -> Nat] /\ \A n \in Node: lastApplied[n] = 0
  /\ leaderId \in [Node -> (Node \cup {NoNode})] /\ \A n \in Node: leaderId[n] = NoNode
  /\ nextIndex \in [Node -> [Node -> Nat]]
  /\ \A i,j \in Node: nextIndex[i][j] = 1
  /\ matchIndex \in [Node -> [Node -> Nat]]
  /\ \A i,j \in Node: matchIndex[i][j] = 0
  /\ electionElapsed \in [Node -> Nat] /\ \A n \in Node: electionElapsed[n] = 0
  /\ electionTimeout \in [Node -> Nat] /\ \A n \in Node: RandTimeout(electionTimeout[n])
  /\ requestElapsed \in [Node -> Nat] /\ \A n \in Node: requestElapsed[n] = 0
  /\ requestTimeout \in [Node -> Nat] /\ \A n \in Node: requestTimeout[n] = RTimeout
  /\ snapshotLastIdx \in [Node -> Nat] /\ \A n \in Node: snapshotLastIdx[n] = 0
  /\ snapshotLastTerm \in [Node -> Nat] /\ \A n \in Node: snapshotLastTerm[n] = 0
  /\ snapshotInProgress \in [Node -> BOOLEAN] /\ \A n \in Node: snapshotInProgress[n] = FALSE
  /\ grantedPrevotes \in [Node -> SUBSET Node] /\ \A n \in Node: grantedPrevotes[n] = {}
  /\ grantedVotes \in [Node -> SUBSET Node] /\ \A n \in Node: grantedVotes[n] = {}
  /\ Net = {}

Next ==
  \/
    \E n \in Node: PeriodicElectionTimeout(n)
  \/
    \E n \in Node: PeriodicHeartbeat(n)
  \/
    \E n \in Node: ElectionStart(n)
  \/
    \E n \in Node: BecomeFollower(n)
  \/
    \E n \in Node: BecomePreCandidate(n)
  \/
    \E n \in Node: BecomeCandidate(n)
  \/
    \E n \in Node: BecomeLeader(n)
  \/
    \E l \in Node, f \in Node: SendAppendEntries(l, f)
  \/
    \E l \in Node, f \in Node: SendHeartbeat(l, f)
  \/
    \E n \in Node: RecvAppendEntries(n)
  \/
    \E n \in Node: RecvAppendEntriesResponse(n)
  \/
    \E n \in Node: RecvRequestVote(n)
  \/
    \E n \in Node: RecvRequestVoteResponse(n)
  \/
    \E l \in Node, ety \in {"DATA","ADD_NODE","REMOVE_NODE"}, x \in Node: LogAppend(l, ety, x)
  \/
    \E n \in Node, i \in Nat: LogDelete(n, i)
  \/
    \E n \in Node: LogCommit(n)
  \/
    \E n \in Node: LogCommitFollower(n)
  \/
    \E n \in Node: ApplyConfigChange(n)
  \/
    \E l \in Node, x \in Node: AddNode(l, x)
  \/
    \E l \in Node, x \in Node: RemoveNode(l, x)
  \/
    \E n \in Node: SnapshotBegin(n)
  \/
    \E n \in Node: SnapshotEnd(n)
  \/
    \E n \in Node: TermAdvanceOnHigherTerm(n)

Spec == Init /\ [][Next]_<< Voters, state, currentTerm, votedFor, log, commitIndex, lastApplied, leaderId, nextIndex, matchIndex, electionElapsed, electionTimeout, requestElapsed, requestTimeout, snapshotLastIdx, snapshotLastTerm, snapshotInProgress, grantedPrevotes, grantedVotes, Net >>

(*
Minimal fix: Replace the bound variable 'n' inside the set comprehensions used to construct RequestVote messages
with 'dest' to avoid SANY's "Unknown operator: `n`" error at those locations. No logic is changed.
Affected actions: BecomePreCandidate, BecomeCandidate, ElectionStartPreCandidate, ElectionStartCandidate.
*)

====