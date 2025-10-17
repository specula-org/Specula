---- MODULE redisraft ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS
    NODES,
    ElectionTimeout,
    HeartbeatTimeout

ASSUME ElectionTimeout \in Nat \ {0}
ASSUME HeartbeatTimeout \in Nat \ {0}

States == {"FOLLOWER","PRECANDIDATE","CANDIDATE","LEADER"}
EntryKinds == {"noop","normal","addVoter","addNonVoter","remove"}
Nil == "NONE"

VARIABLES
    state,
    currentTerm,
    votedFor,
    leaderId,
    log,
    commitIndex,
    lastApplied,
    snapshotLastIndex,
    snapshotLastTerm,
    electionTimeoutRand,
    timeoutElapsed,
    hbElapsed,
    nextIndex,
    matchIndex,
    messages,
    members,
    voting,
    snapshotInProgress,
    prevoteGrants,
    voteGrants

MsgTypes == {"AE","AEResp","RV","RVR"}

MsgSpace ==
    [ type: MsgTypes,
      from: NODES,
      to:   NODES,
      term: Nat,
      prevote: BOOLEAN,
      prevLogIndex: Nat,
      prevLogTerm: Nat,
      leaderCommit: Nat,
      entries: Seq([term:Nat, kind:EntryKinds, node:(NODES \cup {Nil})]),
      success: BOOLEAN,
      matchIndex: Nat,
      requestTerm: Nat,
      voteGranted: BOOLEAN ]

TypeOK ==
    /\ state \in [NODES -> States]
    /\ currentTerm \in [NODES -> Nat]
    /\ votedFor \in [NODES -> (NODES \cup {Nil})]
    /\ leaderId \in [NODES -> (NODES \cup {Nil})]
    /\ log \in [NODES -> Seq([term:Nat, kind:EntryKinds, node:(NODES \cup {Nil})])]
    /\ commitIndex \in [NODES -> Nat]
    /\ lastApplied \in [NODES -> Nat]
    /\ snapshotLastIndex \in [NODES -> Nat]
    /\ snapshotLastTerm \in [NODES -> Nat]
    /\ electionTimeoutRand \in [NODES -> Nat]
    /\ timeoutElapsed \in [NODES -> Nat]
    /\ hbElapsed \in [NODES -> Nat]
    /\ nextIndex \in [NODES -> [NODES -> Nat]]
    /\ matchIndex \in [NODES -> [NODES -> Nat]]
    /\ messages \subseteq MsgSpace
    /\ members \subseteq NODES
    /\ voting \subseteq members
    /\ snapshotInProgress \in [NODES -> BOOLEAN]
    /\ prevoteGrants \in [NODES -> SUBSET NODES]
    /\ voteGrants \in [NODES -> SUBSET NODES]
    /\ \A n \in NODES:
         /\ commitIndex[n] <= snapshotLastIndex[n] + Len(log[n])
         /\ lastApplied[n] <= commitIndex[n]
         /\ nextIndex[n] \in [NODES -> Nat]
         /\ matchIndex[n] \in [NODES -> Nat]
         /\ nextIndex[n][n] = snapshotLastIndex[n] + Len(log[n]) + 1
         /\ matchIndex[n][n] = snapshotLastIndex[n] + Len(log[n])

Voters == voting
QuorumSize == (Cardinality(Voters) \div 2) + 1
QuorumReached(S) == Cardinality(S \cap Voters) >= QuorumSize

LastIndex(n) == snapshotLastIndex[n] + Len(log[n])
LastTerm(n) == IF Len(log[n]) = 0 THEN snapshotLastTerm[n] ELSE log[n][Len(log[n])].term

PosOf(n, idx) == idx - snapshotLastIndex[n]

LogTermAt(n, idx) ==
    IF idx = snapshotLastIndex[n] THEN snapshotLastTerm[n]
    ELSE IF idx > snapshotLastIndex[n] /\ PosOf(n, idx) \in 1..Len(log[n]) THEN log[n][PosOf(n, idx)].term ELSE 0

SuffixFrom(n, idx) ==
    LET p == PosOf(n, idx) IN
      IF idx > snapshotLastIndex[n] /\ p \in 1..Len(log[n]) THEN SubSeq(log[n], p, Len(log[n])) ELSE <<>>

PrefixUntil(n, idx) ==
    LET p == PosOf(n, idx) IN
      IF p <= 0 THEN <<>> ELSE IF p > Len(log[n]) THEN log[n] ELSE SubSeq(log[n], 1, p)

ApplyOverwrite(n, prevIdx, ents) ==
    PrefixUntil(n, prevIdx) \o ents

NoLeader == Nil
EmptyEntries == <<>>

IsLeader(n) == state[n] = "LEADER"
IsCandidate(n) == state[n] = "CANDIDATE"
IsPreCandidate(n) == state[n] = "PRECANDIDATE"
IsFollower(n) == state[n] = "FOLLOWER"

RandomizeTimeoutPrime(n) ==
    \E r \in ElectionTimeout..(2*ElectionTimeout):
      electionTimeoutRand' = [electionTimeoutRand EXCEPT ![n] = r]

BecomeFollower(n) ==
    /\ n \in NODES
    /\ state[n] # "FOLLOWER"
    /\ state' = [state EXCEPT ![n] = "FOLLOWER"]
    /\ leaderId' = [leaderId EXCEPT ![n] = NoLeader]
    /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![n] = 0]
    /\ hbElapsed' = hbElapsed
    /\ currentTerm' = currentTerm
    /\ votedFor' = votedFor
    /\ \E r \in ElectionTimeout..(2*ElectionTimeout):
         electionTimeoutRand' = [electionTimeoutRand EXCEPT ![n] = r]
    /\ UNCHANGED << log, commitIndex, lastApplied, snapshotLastIndex, snapshotLastTerm,
                    nextIndex, matchIndex, messages, members, voting, snapshotInProgress,
                    prevoteGrants, voteGrants >>

BecomePreCandidate(n) ==
    /\ n \in NODES
    /\ ~IsLeader(n)
    /\ state' = [state EXCEPT ![n] = "PRECANDIDATE"]
    /\ \E r \in ElectionTimeout..(2*ElectionTimeout):
         electionTimeoutRand' = [electionTimeoutRand EXCEPT ![n] = r]
    /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![n] = 0]
    /\ leaderId' = [leaderId EXCEPT ![n] = NoLeader]
    /\ prevoteGrants' = [prevoteGrants EXCEPT ![n] = {n} \cap Voters]
    /\ voteGrants' = voteGrants
    /\ votedFor' = votedFor
    /\ hbElapsed' = hbElapsed
    /\ currentTerm' = currentTerm
    /\ messages' =
        LET reqs ==
              { [ type |-> "RV",
                  from |-> n,
                  to |-> m,
                  term |-> currentTerm[n] + 1,
                  prevote |-> TRUE,
                  prevLogIndex |-> LastIndex(n),
                  prevLogTerm |-> LastTerm(n),
                  leaderCommit |-> 0,
                  entries |-> EmptyEntries,
                  success |-> FALSE,
                  matchIndex |-> 0,
                  requestTerm |-> currentTerm[n] + 1,
                  voteGranted |-> FALSE ]
                : m \in Voters /\ m # n }
        IN messages \cup reqs
    /\ UNCHANGED << log, commitIndex, lastApplied, snapshotLastIndex, snapshotLastTerm,
                    nextIndex, matchIndex, members, voting, snapshotInProgress >>

BecomeCandidate(n) ==
    /\ n \in NODES
    /\ state[n] \in {"PRECANDIDATE","FOLLOWER","CANDIDATE"}
    /\ state[n] # "PRECANDIDATE" \/ QuorumReached(prevoteGrants[n])
    /\ currentTerm' = [currentTerm EXCEPT ![n] = currentTerm[n] + 1]
    /\ votedFor' = [votedFor EXCEPT ![n] = n]
    /\ state' = [state EXCEPT ![n] = "CANDIDATE"]
    /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![n] = 0]
    /\ \E r \in ElectionTimeout..(2*ElectionTimeout):
         electionTimeoutRand' = [electionTimeoutRand EXCEPT ![n] = r]
    /\ leaderId' = [leaderId EXCEPT ![n] = NoLeader]
    /\ voteGrants' = [voteGrants EXCEPT ![n] = {n} \cap Voters]
    /\ prevoteGrants' = prevoteGrants
    /\ hbElapsed' = hbElapsed
    /\ messages' =
        LET reqs ==
              { [ type |-> "RV",
                  from |-> n,
                  to |-> m,
                  term |-> currentTerm[n] + 1,
                  prevote |-> FALSE,
                  prevLogIndex |-> LastIndex(n),
                  prevLogTerm |-> LastTerm(n),
                  leaderCommit |-> 0,
                  entries |-> EmptyEntries,
                  success |-> FALSE,
                  matchIndex |-> 0,
                  requestTerm |-> currentTerm[n] + 1,
                  voteGranted |-> FALSE ]
                : m \in Voters /\ m # n }
        IN messages \cup reqs
    /\ UNCHANGED << log, commitIndex, lastApplied, snapshotLastIndex, snapshotLastTerm,
                    nextIndex, matchIndex, members, voting, snapshotInProgress >>

BecomeLeader(n) ==
    /\ n \in NODES
    /\ IsCandidate(n)
    /\ QuorumReached(voteGrants[n])
    /\ state' = [state EXCEPT ![n] = "LEADER"]
    /\ leaderId' = [leaderId EXCEPT ![n] = n]
    /\ hbElapsed' = [hbElapsed EXCEPT ![n] = 0]
    /\ timeoutElapsed' = timeoutElapsed
    /\ log' = [log EXCEPT ![n] = Append(log[n], [term |-> currentTerm[n], kind |-> "noop", node |-> Nil])]
    /\ commitIndex' = commitIndex
    /\ lastApplied' = lastApplied
    /\ snapshotLastIndex' = snapshotLastIndex
    /\ snapshotLastTerm' = snapshotLastTerm
    /\ electionTimeoutRand' = electionTimeoutRand
    /\ currentTerm' = currentTerm
    /\ votedFor' = votedFor
    /\ nextIndex' =
         LET lastOld == LastIndex(n) IN
           [nextIndex EXCEPT ![n] = [m \in NODES |-> lastOld + 2]]
    /\ matchIndex' =
         LET lastOld == LastIndex(n) IN
           [matchIndex EXCEPT ![n] = [m \in NODES |-> IF m = n THEN lastOld + 1 ELSE 0]]
    /\ messages' =
        LET nx == nextIndex'[n]
            beats ==
              { [ type |-> "AE",
                  from |-> n,
                  to |-> m,
                  term |-> currentTerm[n],
                  prevote |-> FALSE,
                  prevLogIndex |-> nx[m] - 1,
                  prevLogTerm |-> LogTermAt(n, nx[m] - 1),
                  leaderCommit |-> commitIndex[n],
                  entries |-> EmptyEntries,
                  success |-> FALSE,
                  matchIndex |-> 0,
                  requestTerm |-> 0,
                  voteGranted |-> FALSE ]
                : m \in members /\ m # n }
        IN messages \cup beats
    /\ UNCHANGED << members, voting, snapshotInProgress, prevoteGrants, voteGrants >>

ElectionStart(n) ==
    /\ n \in NODES
    /\ ~IsLeader(n)
    /\ timeoutElapsed[n] >= electionTimeoutRand[n]
    /\ state' = [state EXCEPT ![n] = "PRECANDIDATE"]
    /\ leaderId' = [leaderId EXCEPT ![n] = NoLeader]
    /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![n] = 0]
    /\ \E r \in ElectionTimeout..(2*ElectionTimeout):
         electionTimeoutRand' = [electionTimeoutRand EXCEPT ![n] = r]
    /\ prevoteGrants' = [prevoteGrants EXCEPT ![n] = {n} \cap Voters]
    /\ voteGrants' = voteGrants
    /\ hbElapsed' = hbElapsed
    /\ currentTerm' = currentTerm
    /\ votedFor' = votedFor
    /\ messages' =
        LET reqs ==
              { [ type |-> "RV",
                  from |-> n,
                  to |-> m,
                  term |-> currentTerm[n] + 1,
                  prevote |-> TRUE,
                  prevLogIndex |-> LastIndex(n),
                  prevLogTerm |-> LastTerm(n),
                  leaderCommit |-> 0,
                  entries |-> EmptyEntries,
                  success |-> FALSE,
                  matchIndex |-> 0,
                  requestTerm |-> currentTerm[n] + 1,
                  voteGranted |-> FALSE ]
                : m \in Voters /\ m # n }
        IN messages \cup reqs
    /\ UNCHANGED << log, commitIndex, lastApplied, snapshotLastIndex, snapshotLastTerm,
                    nextIndex, matchIndex, members, voting, snapshotInProgress >>

ElectionTimeoutAction ==
    \E n \in NODES: ElectionStart(n)

PeriodicElectionTimeout ==
    \E n \in NODES:
      /\ IF IsLeader(n)
         THEN /\ hbElapsed' = [hbElapsed EXCEPT ![n] = hbElapsed[n] + 1]
              /\ timeoutElapsed' = timeoutElapsed
         ELSE /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![n] = timeoutElapsed[n] + 1]
              /\ hbElapsed' = hbElapsed
      /\ UNCHANGED << state, currentTerm, votedFor, leaderId, log, commitIndex, lastApplied,
                      snapshotLastIndex, snapshotLastTerm, electionTimeoutRand, nextIndex, matchIndex,
                      messages, members, voting, snapshotInProgress, prevoteGrants, voteGrants >>

PeriodicHeartbeat ==
    \E n \in NODES:
      /\ IsLeader(n)
      /\ hbElapsed' = [hbElapsed EXCEPT ![n] = hbElapsed[n] + 1]
      /\ UNCHANGED << state, currentTerm, votedFor, leaderId, log, commitIndex, lastApplied,
                      snapshotLastIndex, snapshotLastTerm, electionTimeoutRand, timeoutElapsed, nextIndex, matchIndex,
                      messages, members, voting, snapshotInProgress, prevoteGrants, voteGrants >>

SendHeartbeat ==
    \E n \in NODES:
      /\ IsLeader(n)
      /\ hbElapsed[n] >= HeartbeatTimeout
      /\ hbElapsed' = [hbElapsed EXCEPT ![n] = 0]
      /\ messages' =
          LET beats ==
                { [ type |-> "AE",
                    from |-> n,
                    to |-> m,
                    term |-> currentTerm[n],
                    prevote |-> FALSE,
                    prevLogIndex |-> nextIndex[n][m] - 1,
                    prevLogTerm |-> LogTermAt(n, nextIndex[n][m] - 1),
                    leaderCommit |-> commitIndex[n],
                    entries |-> EmptyEntries,
                    success |-> FALSE,
                    matchIndex |-> 0,
                    requestTerm |-> 0,
                    voteGranted |-> FALSE ]
                  : m \in members /\ m # n }
          IN messages \cup beats
      /\ UNCHANGED << state, currentTerm, votedFor, leaderId, log, commitIndex, lastApplied,
                      snapshotLastIndex, snapshotLastTerm, electionTimeoutRand, timeoutElapsed,
                      nextIndex, matchIndex, members, voting, snapshotInProgress, prevoteGrants, voteGrants >>

SendAppendEntries ==
    \E n \in NODES:
      \E m \in members:
        /\ IsLeader(n) /\ m # n
        /\ nextIndex[n][m] >= 1
        /\ LET fromIdx == nextIndex[n][m]
               ents == SuffixFrom(n, fromIdx)
               prevIdx == fromIdx - 1
            IN
              /\ messages' = messages \cup {
                   [ type |-> "AE",
                     from |-> n,
                     to |-> m,
                     term |-> currentTerm[n],
                     prevote |-> FALSE,
                     prevLogIndex |-> prevIdx,
                     prevLogTerm |-> LogTermAt(n, prevIdx),
                     leaderCommit |-> commitIndex[n],
                     entries |-> ents,
                     success |-> FALSE,
                     matchIndex |-> 0,
                     requestTerm |-> 0,
                     voteGranted |-> FALSE ] }
              /\ UNCHANGED << state, currentTerm, votedFor, leaderId, log, commitIndex, lastApplied,
                              snapshotLastIndex, snapshotLastTerm, electionTimeoutRand, timeoutElapsed,
                              hbElapsed, nextIndex, matchIndex, members, voting, snapshotInProgress,
                              prevoteGrants, voteGrants >>

LogDelete(n, fromIdx) ==
    /\ n \in NODES
    /\ fromIdx > snapshotLastIndex[n]
    /\ \E newLog \in Seq([term:Nat, kind:EntryKinds, node:(NODES \cup {Nil})]):
         /\ newLog = PrefixUntil(n, fromIdx - 1)
         /\ log' = [log EXCEPT ![n] = newLog]
         /\ UNCHANGED << state, currentTerm, votedFor, leaderId, commitIndex, lastApplied,
                         snapshotLastIndex, snapshotLastTerm, electionTimeoutRand, timeoutElapsed,
                         hbElapsed, nextIndex, matchIndex, messages, members, voting, snapshotInProgress,
                         prevoteGrants, voteGrants >>

RecvAppendEntries ==
    \E msg \in messages:
      /\ msg.type = "AE"
      /\ LET n == msg.to
             ldr == msg.from
         IN
           /\ IF msg.term < currentTerm[n] THEN
                 /\ messages' = (messages \ {msg}) \cup {
                      [ type |-> "AEResp",
                        from |-> n,
                        to |-> ldr,
                        term |-> currentTerm[n],
                        prevote |-> FALSE,
                        prevLogIndex |-> 0,
                        prevLogTerm |-> 0,
                        leaderCommit |-> 0,
                        entries |-> EmptyEntries,
                        success |-> FALSE,
                        matchIndex |-> LastIndex(n),
                        requestTerm |-> 0,
                        voteGranted |-> FALSE ] }
                 /\ UNCHANGED << state, currentTerm, votedFor, leaderId, log, commitIndex, lastApplied,
                                 snapshotLastIndex, snapshotLastTerm, electionTimeoutRand, timeoutElapsed,
                                 hbElapsed, nextIndex, matchIndex, members, voting, snapshotInProgress,
                                 prevoteGrants, voteGrants >>
              ELSE
                LET newTerm == IF msg.term > currentTerm[n] THEN msg.term ELSE currentTerm[n]
                    okPrev ==
                      /\ msg.prevLogIndex = snapshotLastIndex[n]
                      /\ msg.prevLogTerm = snapshotLastTerm[n]
                    okPrev2 ==
                      /\ msg.prevLogIndex > snapshotLastIndex[n]
                      /\ PosOf(n, msg.prevLogIndex) \in 1..Len(log[n])
                      /\ LogTermAt(n, msg.prevLogIndex) = msg.prevLogTerm
                IN
                  /\ leaderId' = [leaderId EXCEPT ![n] = ldr]
                  /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![n] = 0]
                  /\ hbElapsed' = hbElapsed
                  /\ electionTimeoutRand' = electionTimeoutRand
                  /\ votedFor' = votedFor
                  /\ state' = [state EXCEPT ![n] = "FOLLOWER"]
                  /\ currentTerm' = [currentTerm EXCEPT ![n] = newTerm]
                  /\ IF okPrev \/ okPrev2 THEN
                        LET newLogN == ApplyOverwrite(n, msg.prevLogIndex, msg.entries)
                            newLog == [log EXCEPT ![n] = newLogN]
                            newLast == snapshotLastIndex[n] + Len(newLog[n])
                            newCommit == IF newLast <= msg.leaderCommit THEN newLast ELSE msg.leaderCommit
                        IN
                          /\ log' = newLog
                          /\ commitIndex' = [commitIndex EXCEPT ![n] = newCommit]
                          /\ messages' = (messages \ {msg}) \cup {
                               [ type |-> "AEResp",
                                 from |-> n,
                                 to |-> ldr,
                                 term |-> currentTerm'[n],
                                 prevote |-> FALSE,
                                 prevLogIndex |-> 0,
                                 prevLogTerm |-> 0,
                                 leaderCommit |-> 0,
                                 entries |-> EmptyEntries,
                                 success |-> TRUE,
                                 matchIndex |-> newLast,
                                 requestTerm |-> 0,
                                 voteGranted |-> FALSE ] }
                     ELSE
                          /\ log' = log
                          /\ commitIndex' = commitIndex
                          /\ messages' = (messages \ {msg}) \cup {
                               [ type |-> "AEResp",
                                 from |-> n,
                                 to |-> ldr,
                                 term |-> currentTerm'[n],
                                 prevote |-> FALSE,
                                 prevLogIndex |-> 0,
                                 prevLogTerm |-> 0,
                                 leaderCommit |-> 0,
                                 entries |-> EmptyEntries,
                                 success |-> FALSE,
                                 matchIndex |-> LastIndex(n),
                                 requestTerm |-> 0,
                                 voteGranted |-> FALSE ] }
                  /\ lastApplied' = lastApplied
                  /\ snapshotLastIndex' = snapshotLastIndex
                  /\ snapshotLastTerm' = snapshotLastTerm
                  /\ nextIndex' = nextIndex
                  /\ matchIndex' = matchIndex
                  /\ UNCHANGED << members, voting, snapshotInProgress, prevoteGrants, voteGrants >>

RecvAppendEntriesResponse ==
    \E msg \in messages:
      /\ msg.type = "AEResp"
      /\ LET ldr == msg.to
             f   == msg.from
         IN
           /\ IsLeader(ldr)
           /\ IF msg.term > currentTerm[ldr] THEN
                /\ messages' = messages \ {msg}
                /\ currentTerm' = [currentTerm EXCEPT ![ldr] = msg.term]
                /\ state' = [state EXCEPT ![ldr] = "FOLLOWER"]
                /\ leaderId' = [leaderId EXCEPT ![ldr] = NoLeader]
                /\ UNCHANGED << votedFor, log, commitIndex, lastApplied, snapshotLastIndex, snapshotLastTerm,
                                electionTimeoutRand, timeoutElapsed, hbElapsed, nextIndex, matchIndex,
                                members, voting, snapshotInProgress, prevoteGrants, voteGrants >>
              ELSE
                /\ currentTerm' = currentTerm
                /\ state' = state
                /\ leaderId' = leaderId
                /\ messages' = messages \ {msg}
                /\ IF msg.success THEN
                     /\ matchIndex' = [matchIndex EXCEPT ![ldr][f] = msg.matchIndex]
                     /\ nextIndex' = [nextIndex EXCEPT ![ldr][f] = msg.matchIndex + 1]
                   ELSE
                     /\ matchIndex' = matchIndex
                     /\ nextIndex' = [nextIndex EXCEPT ![ldr][f] = IF nextIndex[ldr][f] > 1 THEN nextIndex[ldr][f] - 1 ELSE 1]
                /\ commitIndex' = commitIndex
                /\ UNCHANGED << votedFor, log, lastApplied, snapshotLastIndex, snapshotLastTerm,
                                electionTimeoutRand, timeoutElapsed, hbElapsed, members, voting,
                                snapshotInProgress, prevoteGrants, voteGrants >>

LogAppend ==
    \E n \in NODES:
      /\ IsLeader(n)
      /\ \E k \in EntryKinds:
           /\ \E tgt \in (NODES \cup {Nil}):
                /\ log' = [log EXCEPT ![n] = Append(log[n], [term |-> currentTerm[n], kind |-> k, node |-> tgt])]
      /\ UNCHANGED << state, currentTerm, votedFor, leaderId, commitIndex, lastApplied,
                      snapshotLastIndex, snapshotLastTerm, electionTimeoutRand, timeoutElapsed, hbElapsed,
                      nextIndex, matchIndex, messages, members, voting, snapshotInProgress, prevoteGrants, voteGrants >>

LogCommit ==
    \E n \in NODES:
      /\ IsLeader(n)
      /\ \E k \in 0..LastIndex(n):
           /\ k > commitIndex[n]
           /\ LogTermAt(n, k) = currentTerm[n]
           /\ Cardinality(({ m \in Voters: matchIndex[n][m] >= k } \cup {n})) >= QuorumSize
           /\ commitIndex' = [commitIndex EXCEPT ![n] = k]
      /\ UNCHANGED << state, currentTerm, votedFor, leaderId, log, lastApplied, snapshotLastIndex, snapshotLastTerm,
                      electionTimeoutRand, timeoutElapsed, hbElapsed, nextIndex, matchIndex,
                      messages, members, voting, snapshotInProgress, prevoteGrants, voteGrants >>

RecvRequestVote ==
    \E msg \in messages:
      /\ msg.type = "RV"
      /\ LET n == msg.to
             c == msg.from
         IN
           /\ IF msg.prevote THEN
                /\ messages' =
                    LET upToDate ==
                          ~((msg.prevLogTerm < LastTerm(n)) \/
                            (msg.prevLogTerm = LastTerm(n) /\ msg.prevLogIndex < LastIndex(n)))
                        leaderBlocks ==
                          leaderId[n] # NoLeader /\ leaderId[n] # c /\ timeoutElapsed[n] < electionTimeoutRand[n]
                        grant == upToDate /\ ~leaderBlocks
                        resp ==
                          [ type |-> "RVR", from |-> n, to |-> c, term |-> currentTerm[n],
                            prevote |-> TRUE, prevLogIndex |-> 0, prevLogTerm |-> 0, leaderCommit |-> 0,
                            entries |-> EmptyEntries, success |-> grant, matchIndex |-> 0,
                            requestTerm |-> msg.term, voteGranted |-> grant ]
                    IN (messages \ {msg}) \cup {resp}
                /\ UNCHANGED << state, currentTerm, votedFor, leaderId, log, commitIndex, lastApplied,
                                snapshotLastIndex, snapshotLastTerm, electionTimeoutRand, timeoutElapsed, hbElapsed,
                                nextIndex, matchIndex, members, voting, snapshotInProgress, prevoteGrants, voteGrants >>
              ELSE
                LET newTerm == IF msg.term > currentTerm[n] THEN msg.term ELSE currentTerm[n]
                    sameTermVotedOther == (votedFor[n] # Nil /\ votedFor[n] # c /\ currentTerm[n] = msg.term)
                    logOK == ~((msg.prevLogTerm < LastTerm(n)) \/
                               (msg.prevLogTerm = LastTerm(n) /\ msg.prevLogIndex < LastIndex(n)))
                    grant == (newTerm = msg.term) /\ ~sameTermVotedOther /\ logOK
                IN
                  /\ currentTerm' = [currentTerm EXCEPT ![n] = newTerm]
                  /\ votedFor' = IF grant THEN [votedFor EXCEPT ![n] = c] ELSE votedFor
                  /\ leaderId' = [leaderId EXCEPT ![n] = NoLeader]
                  /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![n] = 0]
                  /\ state' = [state EXCEPT ![n] = "FOLLOWER"]
                  /\ electionTimeoutRand' = electionTimeoutRand
                  /\ hbElapsed' = hbElapsed
                  /\ messages' = (messages \ {msg}) \cup {
                        [ type |-> "RVR", from |-> n, to |-> c, term |-> currentTerm'[n],
                          prevote |-> FALSE, prevLogIndex |-> 0, prevLogTerm |-> 0, leaderCommit |-> 0,
                          entries |-> EmptyEntries, success |-> grant, matchIndex |-> 0,
                          requestTerm |-> msg.term, voteGranted |-> grant ] }
                  /\ UNCHANGED << log, commitIndex, lastApplied, snapshotLastIndex, snapshotLastTerm,
                                  nextIndex, matchIndex, members, voting, snapshotInProgress,
                                  prevoteGrants, voteGrants >>

RecvRequestVoteResponse ==
    \E msg \in messages:
      /\ msg.type = "RVR"
      /\ LET n == msg.to
             s == msg.from
         IN
           /\ IF msg.term > currentTerm[n] THEN
                /\ messages' = messages \ {msg}
                /\ currentTerm' = [currentTerm EXCEPT ![n] = msg.term]
                /\ state' = [state EXCEPT ![n] = "FOLLOWER"]
                /\ leaderId' = [leaderId EXCEPT ![n] = NoLeader]
                /\ UNCHANGED << votedFor, log, commitIndex, lastApplied, snapshotLastIndex, snapshotLastTerm,
                                electionTimeoutRand, timeoutElapsed, hbElapsed, nextIndex, matchIndex,
                                members, voting, snapshotInProgress, prevoteGrants, voteGrants >>
              ELSE
                /\ currentTerm' = currentTerm
                /\ leaderId' = leaderId
                /\ messages' = messages \ {msg}
                /\ IF msg.prevote /\ IsPreCandidate(n) /\ msg.requestTerm = currentTerm[n] + 1 /\ msg.voteGranted
                   THEN /\ prevoteGrants' = [prevoteGrants EXCEPT ![n] = prevoteGrants[n] \cup {s}]
                        /\ voteGrants' = voteGrants
                        /\ state' = state
                   ELSE IF ~msg.prevote /\ IsCandidate(n) /\ msg.requestTerm = currentTerm[n] /\ msg.voteGranted
                        THEN /\ voteGrants' = [voteGrants EXCEPT ![n] = voteGrants[n] \cup {s}]
                             /\ prevoteGrants' = prevoteGrants
                             /\ state' = state
                        ELSE /\ prevoteGrants' = prevoteGrants
                             /\ voteGrants' = voteGrants
                             /\ state' = state
                /\ UNCHANGED << votedFor, log, commitIndex, lastApplied, snapshotLastIndex, snapshotLastTerm,
                                electionTimeoutRand, timeoutElapsed, hbElapsed, nextIndex, matchIndex,
                                members, voting, snapshotInProgress >>

AddNode ==
    \E n \in NODES:
      /\ IsLeader(n)
      /\ \E x \in (NODES \ members):
           /\ log' = [log EXCEPT ![n] = Append(log[n], [term |-> currentTerm[n], kind |-> "addVoter", node |-> x])]
      /\ UNCHANGED << state, currentTerm, votedFor, leaderId, commitIndex, lastApplied,
                      snapshotLastIndex, snapshotLastTerm, electionTimeoutRand, timeoutElapsed, hbElapsed,
                      nextIndex, matchIndex, messages, members, voting, snapshotInProgress, prevoteGrants, voteGrants >>

RemoveNode ==
    \E n \in NODES:
      /\ IsLeader(n)
      /\ \E x \in members:
           /\ log' = [log EXCEPT ![n] = Append(log[n], [term |-> currentTerm[n], kind |-> "remove", node |-> x])]
      /\ UNCHANGED << state, currentTerm, votedFor, leaderId, commitIndex, lastApplied,
                      snapshotLastIndex, snapshotLastTerm, electionTimeoutRand, timeoutElapsed, hbElapsed,
                      nextIndex, matchIndex, messages, members, voting, snapshotInProgress, prevoteGrants, voteGrants >>

ApplyConfigChange ==
    \E n \in NODES:
      /\ lastApplied[n] < commitIndex[n]
      /\ \E idx \in (lastApplied[n]+1)..commitIndex[n]:
          LET e == IF idx = snapshotLastIndex[n]
                   THEN [term |-> snapshotLastTerm[n], kind |-> "noop", node |-> Nil]
                   ELSE log[n][PosOf(n, idx)]
          IN
            /\ members' =
                IF e.kind = "addVoter" THEN members \cup {e.node}
                ELSE IF e.kind = "addNonVoter" THEN members \cup {e.node}
                ELSE IF e.kind = "remove" THEN members \ {e.node}
                ELSE members
            /\ voting' =
                IF e.kind = "addVoter" THEN voting \cup {e.node}
                ELSE IF e.kind = "addNonVoter" THEN voting \ {e.node}
                ELSE IF e.kind = "remove" THEN voting \ {e.node}
                ELSE voting
            /\ lastApplied' = [lastApplied EXCEPT ![n] = idx]
      /\ UNCHANGED << state, currentTerm, votedFor, leaderId, log, commitIndex,
                      snapshotLastIndex, snapshotLastTerm, electionTimeoutRand, timeoutElapsed, hbElapsed,
                      nextIndex, matchIndex, messages, snapshotInProgress, prevoteGrants, voteGrants >>

SnapshotBegin ==
    \E n \in NODES:
      /\ ~snapshotInProgress[n]
      /\ commitIndex[n] > snapshotLastIndex[n]
      /\ snapshotInProgress' = [snapshotInProgress EXCEPT ![n] = TRUE]
      /\ UNCHANGED << state, currentTerm, votedFor, leaderId, log, commitIndex, lastApplied,
                      snapshotLastIndex, snapshotLastTerm, electionTimeoutRand, timeoutElapsed, hbElapsed,
                      nextIndex, matchIndex, messages, members, voting, prevoteGrants, voteGrants >>

SnapshotEnd ==
    \E n \in NODES:
      /\ snapshotInProgress[n]
      /\ \E sIdx \in snapshotLastIndex[n]..commitIndex[n]:
          /\ snapshotLastIndex' = [snapshotLastIndex EXCEPT ![n] = commitIndex[n]]
          /\ snapshotLastTerm' = [snapshotLastTerm EXCEPT ![n] = LogTermAt(n, commitIndex[n])]
          /\ log' = [log EXCEPT ![n] =
                        LET dropCount == PosOf(n, commitIndex[n])
                        IN SubSeq(log[n], dropCount + 1, Len(log[n]))]
          /\ snapshotInProgress' = [snapshotInProgress EXCEPT ![n] = FALSE]
      /\ UNCHANGED << state, currentTerm, votedFor, leaderId, commitIndex, lastApplied,
                      electionTimeoutRand, timeoutElapsed, hbElapsed, nextIndex, matchIndex,
                      messages, members, voting, prevoteGrants, voteGrants >>

Init ==
    /\ state = [n \in NODES |-> "FOLLOWER"]
    /\ currentTerm = [n \in NODES |-> 0]
    /\ votedFor = [n \in NODES |-> Nil]
    /\ leaderId = [n \in NODES |-> NoLeader]
    /\ log = [n \in NODES |-> <<>>]
    /\ commitIndex = [n \in NODES |-> 0]
    /\ lastApplied = [n \in NODES |-> 0]
    /\ snapshotLastIndex = [n \in NODES |-> 0]
    /\ snapshotLastTerm = [n \in NODES |-> 0]
    /\ \A n \in NODES: \E r \in ElectionTimeout..(2*ElectionTimeout): electionTimeoutRand[n] = r
    /\ timeoutElapsed = [n \in NODES |-> 0]
    /\ hbElapsed = [n \in NODES |-> 0]
    /\ nextIndex = [n \in NODES |-> [m \in NODES |-> 1]]
    /\ matchIndex = [n \in NODES |-> [m \in NODES |-> 0]]
    /\ messages = {}
    /\ members = NODES
    /\ voting = NODES
    /\ snapshotInProgress = [n \in NODES |-> FALSE]
    /\ prevoteGrants = [n \in NODES |-> {}]
    /\ voteGrants = [n \in NODES |-> {}]
    /\ TypeOK

vars == <<state, currentTerm, votedFor, leaderId, log, commitIndex, lastApplied,
          snapshotLastIndex, snapshotLastTerm, electionTimeoutRand, timeoutElapsed, hbElapsed,
          nextIndex, matchIndex, messages, members, voting, snapshotInProgress, prevoteGrants, voteGrants>>

Next ==
    \/ PeriodicElectionTimeout
    \/ PeriodicHeartbeat
    \/ ElectionTimeoutAction
    \/ \E n \in NODES: BecomePreCandidate(n)
    \/ \E n \in NODES: BecomeCandidate(n)
    \/ \E n \in NODES: BecomeFollower(n)
    \/ \E n \in NODES: BecomeLeader(n)
    \/ SendHeartbeat
    \/ SendAppendEntries
    \/ RecvAppendEntries
    \/ RecvAppendEntriesResponse
    \/ RecvRequestVote
    \/ RecvRequestVoteResponse
    \/ LogAppend
    \/ \E n \in NODES, i \in Nat: LogDelete(n, i)
    \/ LogCommit
    \/ AddNode
    \/ RemoveNode
    \/ ApplyConfigChange
    \/ SnapshotBegin
    \/ SnapshotEnd

Spec == Init /\ [][Next]_vars

====