---- MODULE redisraft ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS
  Nodes,
  Null,
  ElectionTimeout,
  RequestTimeout

ASSUME Null \notin Nodes

Entry ==
  [term: Nat,
   type: {"NOOP","NORMAL","ADD_NODE","ADD_NONVOTING_NODE","REMOVE_NODE"},
   node: Nodes \cup {Null}]

Vars ==
  << state, currentTerm, votedFor, log, commitIndex, lastApplied, leaderId,
     nextIndex, matchIndex, electionTimeoutRand, timeoutElapsed,
     Members, Voting, snapshotLastIndex, snapshotLastTerm, snapshotInProgress,
     msgs, votesReceived, prevotesReceived >>

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
  electionTimeoutRand,
  timeoutElapsed,
  Members,
  Voting,
  snapshotLastIndex,
  snapshotLastTerm,
  snapshotInProgress,
  msgs,
  votesReceived,
  prevotesReceived

RandRange == { k \in Nat : ElectionTimeout <= k /\ k < 2*ElectionTimeout }

LastIndex(n) == Len(log[n])

TermAt(n, i) ==
  IF i = 0 THEN snapshotLastTerm[n]
  ELSE log[n][i].term

LastTerm(n) ==
  IF LastIndex(n) = 0 THEN snapshotLastTerm[n] ELSE TermAt(n, LastIndex(n))

UpToDate(llIdx, llTerm, n) ==
  \/ llTerm > LastTerm(n)
  \/ /\ llTerm = LastTerm(n)
     /\ llIdx >= LastIndex(n)

Quorum(S) == Cardinality(S) > Cardinality(Voting) \div 2

AERecord(from, to, term, pli, plt, ents, lcmt) ==
  [type |-> "AE", from |-> from, to |-> to, term |-> term,
   prevLogIndex |-> pli, prevLogTerm |-> plt, entries |-> ents, leaderCommit |-> lcmt]

AERRecord(from, to, term, success, mi) ==
  [type |-> "AER", from |-> from, to |-> to, term |-> term, success |-> success, matchIndex |-> mi]

RVRecord(from, to, term, lli, llt, pv) ==
  [type |-> "RV", from |-> from, to |-> to, term |-> term,
   lastLogIndex |-> lli, lastLogTerm |-> llt, prevote |-> pv]

RVRRecord(from, to, term, granted, rterm, pv) ==
  [type |-> "RVR", from |-> from, to |-> to, term |-> term,
   voteGranted |-> granted, requestTerm |-> rterm, prevote |-> pv]

Init ==
  /\ state \in [Nodes -> {"FOLLOWER","PRECANDIDATE","CANDIDATE","LEADER"}]
  /\ state = [n \in Nodes |-> "FOLLOWER"]
  /\ currentTerm \in [Nodes -> Nat]
  /\ currentTerm = [n \in Nodes |-> 0]
  /\ votedFor \in [Nodes -> (Nodes \cup {Null})]
  /\ votedFor = [n \in Nodes |-> Null]
  /\ log \in [Nodes -> Seq(Entry)]
  /\ log = [n \in Nodes |-> << >>]
  /\ commitIndex \in [Nodes -> Nat]
  /\ commitIndex = [n \in Nodes |-> 0]
  /\ lastApplied \in [Nodes -> Nat]
  /\ lastApplied = [n \in Nodes |-> 0]
  /\ leaderId \in [Nodes -> (Nodes \cup {Null})]
  /\ leaderId = [n \in Nodes |-> Null]
  /\ nextIndex \in [Nodes -> [Nodes -> Nat]]
  /\ nextIndex = [l \in Nodes |-> [m \in Nodes |-> 1]]
  /\ matchIndex \in [Nodes -> [Nodes -> Nat]]
  /\ matchIndex = [l \in Nodes |-> [m \in Nodes |-> 0]]
  /\ electionTimeoutRand \in [Nodes -> Nat]
  /\ electionTimeoutRand \in [Nodes -> RandRange]
  /\ timeoutElapsed \in [Nodes -> Nat]
  /\ timeoutElapsed = [n \in Nodes |-> 0]
  /\ Members \subseteq Nodes
  /\ Members = Nodes
  /\ Voting \subseteq Members
  /\ Voting = Members
  /\ snapshotLastIndex \in [Nodes -> Nat]
  /\ snapshotLastIndex = [n \in Nodes |-> 0]
  /\ snapshotLastTerm \in [Nodes -> Nat]
  /\ snapshotLastTerm = [n \in Nodes |-> 0]
  /\ snapshotInProgress \in [Nodes -> BOOLEAN]
  /\ snapshotInProgress = [n \in Nodes |-> FALSE]
  /\ msgs = {}
  /\ votesReceived \in [Nodes -> SUBSET Voting]
  /\ votesReceived = [n \in Nodes |-> {}]
  /\ prevotesReceived \in [Nodes -> SUBSET Voting]
  /\ prevotesReceived = [n \in Nodes |-> {}]

BecomeFollower(n) ==
  /\ n \in Nodes
  /\ state[n] # "FOLLOWER"
  /\ state' = [state EXCEPT ![n] = "FOLLOWER"]
  /\ leaderId' = [leaderId EXCEPT ![n] = Null]
  /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![n] = 0]
  /\ electionTimeoutRand' = [electionTimeoutRand EXCEPT ![n] = CHOOSE k \in RandRange : TRUE]
    \* FIX: EXCEPT requires an expression on the RHS; choose an arbitrary value from RandRange
  /\ UNCHANGED << currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex,
                  Members, Voting, snapshotLastIndex, snapshotLastTerm, snapshotInProgress,
                  msgs, votesReceived, prevotesReceived >>

BecomePreCandidate(n) ==
  /\ n \in Nodes
  /\ state[n] # "LEADER"
  /\ state' = [state EXCEPT ![n] = "PRECANDIDATE"]
  /\ LET reqTerm == currentTerm[n] + 1 IN
     /\ msgs' = msgs \cup { RVRecord(n, v, reqTerm, LastIndex(n), LastTerm(n), TRUE)
                             : v \in (Voting \cap Members) \ {n} }
     \* FIX: Added parentheses to disambiguate intersection with set difference
  /\ prevotesReceived' = [prevotesReceived EXCEPT ![n] = {}]
  /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![n] = 0]
  /\ UNCHANGED << currentTerm, votedFor, log, commitIndex, lastApplied, leaderId,
                  nextIndex, matchIndex, electionTimeoutRand, Members, Voting,
                  snapshotLastIndex, snapshotLastTerm, snapshotInProgress,
                  votesReceived >>

ElectionStart(n) == BecomePreCandidate(n)

BecomeCandidate(n) ==
  /\ n \in Nodes
  /\ state[n] = "PRECANDIDATE"
  /\ currentTerm' = [currentTerm EXCEPT ![n] = currentTerm[n] + 1]
  /\ state' = [state EXCEPT ![n] = "CANDIDATE"]
  /\ votedFor' = [votedFor EXCEPT ![n] = n]
  /\ votesReceived' = [votesReceived EXCEPT ![n] = (IF n \in Voting THEN {n} ELSE {})]
  /\ msgs' = msgs \cup { RVRecord(n, v, currentTerm[n] + 1, LastIndex(n), LastTerm(n), FALSE)
                         : v \in (Voting \cap Members) \ {n} }
     \* FIX: Added parentheses to disambiguate intersection with set difference
  /\ leaderId' = [leaderId EXCEPT ![n] = Null]
  /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![n] = 0]
  /\ UNCHANGED << log, commitIndex, lastApplied, nextIndex, matchIndex,
                  electionTimeoutRand, Members, Voting,
                  snapshotLastIndex, snapshotLastTerm, snapshotInProgress,
                  prevotesReceived >>

BecomeLeader(n) ==
  /\ n \in Nodes
  /\ state[n] = "CANDIDATE"
  /\ LET newlog == Append(log[n], [term |-> currentTerm[n], type |-> "NOOP", node |-> Null]) IN
     /\ state' = [state EXCEPT ![n] = "LEADER"]
     /\ log' = [log EXCEPT ![n] = newlog]
     /\ leaderId' = [leaderId EXCEPT ![n] = n]
     /\ LET li == Len(newlog) IN
        /\ nextIndex' = [nextIndex EXCEPT ![n] = [m \in Nodes |-> li + 1]]
        /\ matchIndex' = [matchIndex EXCEPT ![n] = [m \in Nodes |-> 0]]
        /\ msgs' =
             msgs \cup { AERecord(n, m, currentTerm[n], li, currentTerm[n], << >>, commitIndex[n])
                         : m \in Members \ {n} }
     /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![n] = 0]
  /\ UNCHANGED << currentTerm, votedFor, commitIndex, lastApplied,
                  electionTimeoutRand, Members, Voting, snapshotLastIndex, snapshotLastTerm,
                  snapshotInProgress, votesReceived, prevotesReceived >>

SendAppendEntries(l, m) ==
  /\ l \in Nodes /\ m \in Members /\ l # m
  /\ state[l] = "LEADER"
  /\ LET ni == nextIndex[l][m] IN
     /\ LET ents == IF ni <= Len(log[l]) THEN SubSeq(log[l], ni, Len(log[l])) ELSE << >> IN
        /\ msgs' = msgs \cup { AERecord(l, m, currentTerm[l], ni - 1, TermAt(l, ni - 1), ents, commitIndex[l]) }
        /\ nextIndex' = nextIndex
        /\ matchIndex' = matchIndex
  /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, lastApplied, leaderId,
                  electionTimeoutRand, timeoutElapsed, Members, Voting, snapshotLastIndex, snapshotLastTerm,
                  snapshotInProgress, votesReceived, prevotesReceived >>

SendHeartbeat(l) ==
  /\ l \in Nodes
  /\ state[l] = "LEADER"
  /\ msgs' = msgs \cup { AERecord(l, m, currentTerm[l], Len(log[l]), TermAt(l, Len(log[l])), << >>, commitIndex[l])
                         : m \in Members \ {l} }
  /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![l] = 0]
  /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, lastApplied, leaderId,
                  nextIndex, matchIndex, electionTimeoutRand, Members, Voting,
                  snapshotLastIndex, snapshotLastTerm, snapshotInProgress, votesReceived, prevotesReceived >>

RecvRequestVote(n) ==
  /\ \E m \in msgs :
       /\ m.type = "RV" /\ m.to = n
       /\ LET termNew ==
              IF m.term > currentTerm[n] THEN m.term ELSE currentTerm[n]
          IN
            /\ currentTerm' = [currentTerm EXCEPT ![n] = termNew]
            /\ /\ IF m.term > currentTerm[n] THEN state' = [state EXCEPT ![n] = "FOLLOWER"] ELSE state' = state
               /\ IF m.term > currentTerm[n] THEN votedFor' = [votedFor EXCEPT ![n] = Null] ELSE votedFor' = votedFor
            /\ /\ IF m.prevote
                  THEN
                    /\ LET grant == ( /\ (leaderId[n] = Null \/ timeoutElapsed[n] >= electionTimeoutRand[n])
                                      /\ UpToDate(m.lastLogIndex, m.lastLogTerm, n) )
                       IN msgs' = (msgs \ {m}) \cup { RVRRecord(n, m.from, currentTerm'[n], grant, m.term, TRUE) }
                    /\ timeoutElapsed' = timeoutElapsed
                    /\ leaderId' = leaderId
                  ELSE
                    /\ IF m.term < currentTerm[n]
                       THEN /\ msgs' = (msgs \ {m}) \cup { RVRRecord(n, m.from, currentTerm[n], FALSE, m.term, FALSE) }
                       ELSE
                         /\ LET canVote ==
                                /\ (votedFor[n] = Null \/ votedFor[n] = m.from)
                                /\ UpToDate(m.lastLogIndex, m.lastLogTerm, n)
                            IN
                              /\ msgs' = (msgs \ {m}) \cup { RVRRecord(n, m.from, currentTerm'[n], canVote, m.term, FALSE) }
                              /\ votedFor' =
                                   IF canVote THEN [votedFor EXCEPT ![n] = m.from] ELSE votedFor
                              /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![n] = IF canVote THEN 0 ELSE timeoutElapsed[n]]
                              /\ leaderId' = [leaderId EXCEPT ![n] = IF canVote THEN Null ELSE leaderId[n]]
  /\ UNCHANGED << log, commitIndex, lastApplied, nextIndex, matchIndex, electionTimeoutRand,
                  Members, Voting, snapshotLastIndex, snapshotLastTerm, snapshotInProgress,
                  votesReceived, prevotesReceived >>

RecvRequestVoteResponse(n) ==
  /\ \E r \in msgs :
       /\ r.type = "RVR" /\ r.to = n
       /\ LET newTerm ==
              IF r.term > currentTerm[n] THEN r.term ELSE currentTerm[n]
          IN
            /\ currentTerm' = [currentTerm EXCEPT ![n] = newTerm]
            /\ IF r.term > currentTerm[n]
               THEN /\ state' = [state EXCEPT ![n] = "FOLLOWER"]
                    /\ votedFor' = [votedFor EXCEPT ![n] = Null]
                    /\ msgs' = msgs \ {r}
                    /\ UNCHANGED << votesReceived, prevotesReceived >>
               ELSE
                 /\ /\ IF r.prevote
                       THEN
                         /\ IF state[n] = "PRECANDIDATE" /\ r.requestTerm = currentTerm[n] + 1 /\ r.voteGranted
                            THEN prevotesReceived' = [prevotesReceived EXCEPT ![n] = prevotesReceived[n] \cup {r.from}]
                            ELSE prevotesReceived' = prevotesReceived
                         /\ votesReceived' = votesReceived
                       ELSE
                         /\ IF state[n] = "CANDIDATE" /\ r.requestTerm = currentTerm[n] /\ r.voteGranted
                            THEN votesReceived' = [votesReceived EXCEPT ![n] = votesReceived[n] \cup {r.from}]
                            ELSE votesReceived' = votesReceived
                    /\ msgs' = msgs \ {r}
                    /\ state' = state
                    /\ votedFor' = votedFor
  /\ UNCHANGED << log, commitIndex, lastApplied, leaderId, nextIndex, matchIndex,
                  electionTimeoutRand, timeoutElapsed, Members, Voting,
                  snapshotLastIndex, snapshotLastTerm, snapshotInProgress >>

PromoteAfterPrevote(n) ==
  /\ n \in Nodes
  /\ state[n] = "PRECANDIDATE"
  /\ Quorum(prevotesReceived[n])
  /\ BecomeCandidate(n)

PromoteAfterVote(n) ==
  /\ n \in Nodes
  /\ state[n] = "CANDIDATE"
  /\ Quorum(votesReceived[n])
  /\ BecomeLeader(n)

RecvAppendEntries(n) ==
  /\ \E m \in msgs :
       /\ m.type = "AE" /\ m.to = n
       /\ LET termNew ==
              IF m.term > currentTerm[n] THEN m.term ELSE currentTerm[n]
          IN
            /\ currentTerm' = [currentTerm EXCEPT ![n] = termNew]
            /\ IF m.term < currentTerm[n]
               THEN
                 /\ msgs' = (msgs \ {m}) \cup { AERRecord(n, m.from, currentTerm[n], FALSE, LastIndex(n)) }
                 /\ state' = state
                 /\ leaderId' = leaderId
                 /\ timeoutElapsed' = timeoutElapsed
                 /\ UNCHANGED << votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex,
                                 electionTimeoutRand, Members, Voting, snapshotLastIndex, snapshotLastTerm,
                                 snapshotInProgress, votesReceived, prevotesReceived >>
               ELSE
                 /\ state' = [state EXCEPT ![n] = "FOLLOWER"]
                 /\ leaderId' = [leaderId EXCEPT ![n] = m.from]
                 /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![n] = 0]
                 /\ IF m.prevLogIndex <= LastIndex(n)
                       /\ TermAt(n, m.prevLogIndex) = m.prevLogTerm
                    THEN
                      /\ LET prefix == SubSeq(log[n], 1, m.prevLogIndex)
                             newlog == IF Len(m.entries) = 0 THEN log[n] ELSE prefix \o m.entries
                         IN
                           /\ log' = [log EXCEPT ![n] = newlog]
                           /\ msgs' = (msgs \ {m}) \cup { AERRecord(n, m.from, currentTerm'[n], TRUE, Len(newlog)) }
                           /\ commitIndex' = [commitIndex EXCEPT ![n] =
                                 IF m.leaderCommit <= Len(newlog) THEN m.leaderCommit ELSE Len(newlog)]
                           /\ UNCHANGED << votedFor, lastApplied, nextIndex, matchIndex,
                                           electionTimeoutRand, Members, Voting, snapshotLastIndex, snapshotLastTerm,
                                           snapshotInProgress, votesReceived, prevotesReceived >>
                    ELSE
                      /\ msgs' = (msgs \ {m}) \cup { AERRecord(n, m.from, currentTerm'[n], FALSE, LastIndex(n)) }
                      /\ UNCHANGED << votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex,
                                      electionTimeoutRand, Members, Voting, snapshotLastIndex, snapshotLastTerm,
                                      snapshotInProgress, votesReceived, prevotesReceived >>

RecvAppendEntriesResponse(l) ==
  /\ \E r \in msgs :
       /\ r.type = "AER" /\ r.to = l /\ state[l] = "LEADER"
       /\ IF r.term > currentTerm[l]
          THEN
            /\ currentTerm' = [currentTerm EXCEPT ![l] = r.term]
            /\ state' = [state EXCEPT ![l] = "FOLLOWER"]
            /\ votedFor' = [votedFor EXCEPT ![l] = Null]
            /\ msgs' = msgs \ {r}
            /\ UNCHANGED << log, commitIndex, lastApplied, leaderId, nextIndex, matchIndex,
                            electionTimeoutRand, timeoutElapsed, Members, Voting,
                            snapshotLastIndex, snapshotLastTerm, snapshotInProgress,
                            votesReceived, prevotesReceived >>
          ELSE
            /\ msgs' = msgs \ {r}
            /\ IF r.success
               THEN
                 /\ matchIndex' = [matchIndex EXCEPT ![l] = [matchIndex[l] EXCEPT ![r.from] = r.matchIndex]]
                 /\ nextIndex'  = [nextIndex  EXCEPT ![l] = [nextIndex[l]  EXCEPT ![r.from] = r.matchIndex + 1]]
               ELSE
                 /\ matchIndex' = matchIndex
                 /\ nextIndex'  = [nextIndex EXCEPT ![l] = [nextIndex[l] EXCEPT ![r.from] =
                                      IF nextIndex[l][r.from] > 1 THEN nextIndex[l][r.from] - 1 ELSE 1]]
            /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, lastApplied, leaderId,
                            electionTimeoutRand, timeoutElapsed, Members, Voting,
                            snapshotLastIndex, snapshotLastTerm, snapshotInProgress,
                            votesReceived, prevotesReceived >>

LogCommit(l) ==
  /\ l \in Nodes /\ state[l] = "LEADER"
  /\ \E k \in 0..Len(log[l]) :
       /\ k > commitIndex[l]
       /\ log[l][k].term = currentTerm[l]
       /\ Quorum({ v \in Voting : (v = l) \/ matchIndex[l][v] >= k })
       /\ commitIndex' = [commitIndex EXCEPT ![l] = k]
  /\ UNCHANGED << state, currentTerm, votedFor, log, lastApplied, leaderId,
                  nextIndex, matchIndex, electionTimeoutRand, timeoutElapsed, Members, Voting,
                  snapshotLastIndex, snapshotLastTerm, snapshotInProgress, msgs, votesReceived, prevotesReceived >>

LogAppend(l) ==
  /\ l \in Nodes /\ state[l] = "LEADER"
  /\ \E et \in {"NORMAL","ADD_NODE","ADD_NONVOTING_NODE","REMOVE_NODE"} :
       /\ \E tgt \in (Nodes \cup {Null}) :
            /\ log' = [log EXCEPT ![l] = Append(log[l], [term |-> currentTerm[l], type |-> et, node |-> tgt])]
            /\ UNCHANGED << state, currentTerm, votedFor, commitIndex, lastApplied, leaderId,
                            nextIndex, matchIndex, electionTimeoutRand, timeoutElapsed, Members, Voting,
                            snapshotLastIndex, snapshotLastTerm, snapshotInProgress, msgs, votesReceived, prevotesReceived >>

LogDelete(n) ==
  /\ \E m \in msgs :
       /\ m.type = "AE" /\ m.to = n
       /\ m.prevLogIndex <= LastIndex(n)
       /\ TermAt(n, m.prevLogIndex) # m.prevLogTerm
       /\ m.prevLogIndex > commitIndex[n]
       /\ log' = [log EXCEPT ![n] = SubSeq(log[n], 1, m.prevLogIndex)]
       /\ msgs' = (msgs \ {m}) \cup { AERRecord(n, m.from, currentTerm[n], FALSE, LastIndex(n)) }
  /\ UNCHANGED << state, currentTerm, votedFor, commitIndex, lastApplied, leaderId,
                  nextIndex, matchIndex, electionTimeoutRand, timeoutElapsed, Members, Voting,
                  snapshotLastIndex, snapshotLastTerm, snapshotInProgress, votesReceived, prevotesReceived >>

ApplyConfigChange(n) ==
  /\ n \in Nodes
  /\ lastApplied[n] < commitIndex[n]
  /\ \E idx \in 1..Len(log[n]) :
       /\ idx = lastApplied[n] + 1
       /\ log[n][idx].type \in {"ADD_NODE","ADD_NONVOTING_NODE","REMOVE_NODE"}
       /\ lastApplied' = [lastApplied EXCEPT ![n] = idx]
       /\ IF log[n][idx].type = "ADD_NODE"
          THEN /\ Members' = Members \cup {log[n][idx].node}
               /\ Voting'  = Voting \cup {log[n][idx].node}
          ELSE IF log[n][idx].type = "ADD_NONVOTING_NODE"
               THEN /\ Members' = Members \cup {log[n][idx].node}
                    /\ Voting' = Voting \ {log[n][idx].node}
               ELSE /\ Members' = Members \ {log[n][idx].node}
                    /\ Voting'  = Voting \ {log[n][idx].node}
  /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, leaderId,
                  nextIndex, matchIndex, electionTimeoutRand, timeoutElapsed,
                  snapshotLastIndex, snapshotLastTerm, snapshotInProgress, msgs, votesReceived, prevotesReceived >>

AddNode(n) ==
  /\ n \in Nodes
  /\ lastApplied[n] < commitIndex[n]
  /\ \E idx \in 1..Len(log[n]) :
       /\ idx = lastApplied[n] + 1
       /\ log[n][idx].type \in {"ADD_NODE","ADD_NONVOTING_NODE"}
       /\ lastApplied' = [lastApplied EXCEPT ![n] = idx]
       /\ IF log[n][idx].type = "ADD_NODE"
          THEN /\ Members' = Members \cup {log[n][idx].node}
               /\ Voting'  = Voting \cup {log[n][idx].node}
          ELSE /\ Members' = Members \cup {log[n][idx].node}
               /\ Voting'  = Voting \ {log[n][idx].node}
  /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, leaderId,
                  nextIndex, matchIndex, electionTimeoutRand, timeoutElapsed,
                  snapshotLastIndex, snapshotLastTerm, snapshotInProgress, msgs, votesReceived, prevotesReceived >>

RemoveNode(n) ==
  /\ n \in Nodes
  /\ lastApplied[n] < commitIndex[n]
  /\ \E idx \in 1..Len(log[n]) :
       /\ idx = lastApplied[n] + 1
       /\ log[n][idx].type = "REMOVE_NODE"
       /\ lastApplied' = [lastApplied EXCEPT ![n] = idx]
       /\ Members' = Members \ {log[n][idx].node}
       /\ Voting'  = Voting \ {log[n][idx].node}
  /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, leaderId,
                  nextIndex, matchIndex, electionTimeoutRand, timeoutElapsed,
                  snapshotLastIndex, snapshotLastTerm, snapshotInProgress, msgs, votesReceived, prevotesReceived >>

SnapshotBegin(n) ==
  /\ n \in Nodes
  /\ ~snapshotInProgress[n]
  /\ lastApplied[n] > snapshotLastIndex[n]
  /\ snapshotInProgress' = [snapshotInProgress EXCEPT ![n] = TRUE]
  /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, lastApplied, leaderId,
                  nextIndex, matchIndex, electionTimeoutRand, timeoutElapsed, Members, Voting,
                  snapshotLastIndex, snapshotLastTerm, msgs, votesReceived, prevotesReceived >>

SnapshotEnd(n) ==
  /\ n \in Nodes
  /\ snapshotInProgress[n]
  /\ snapshotLastIndex' = [snapshotLastIndex EXCEPT ![n] = lastApplied[n]]
  /\ snapshotLastTerm' = [snapshotLastTerm EXCEPT ![n] = TermAt(n, lastApplied[n])]
  /\ log' = [log EXCEPT ![n] =
                IF lastApplied[n] < Len(log[n])
                THEN SubSeq(log[n], lastApplied[n] + 1, Len(log[n]))
                ELSE << >>]
  /\ snapshotInProgress' = [snapshotInProgress EXCEPT ![n] = FALSE]
  /\ UNCHANGED << state, currentTerm, votedFor, commitIndex, lastApplied, leaderId,
                  nextIndex, matchIndex, electionTimeoutRand, timeoutElapsed, Members, Voting,
                  msgs, votesReceived, prevotesReceived >>

ElectionTimeout(n) ==
  /\ n \in Nodes
  /\ state[n] # "LEADER"
  /\ timeoutElapsed[n] >= electionTimeoutRand[n]
  /\ ElectionStart(n)

PeriodicElectionTimeout(n) ==
  /\ n \in Nodes
  /\ state[n] # "LEADER"
  /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![n] = timeoutElapsed[n] + 1]
  /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, lastApplied, leaderId,
                  nextIndex, matchIndex, electionTimeoutRand, Members, Voting,
                  snapshotLastIndex, snapshotLastTerm, snapshotInProgress, msgs, votesReceived, prevotesReceived >>

PeriodicHeartbeat(l) ==
  /\ l \in Nodes
  /\ state[l] = "LEADER"
  /\ timeoutElapsed' = [timeoutElapsed EXCEPT ![l] = timeoutElapsed[l] + 1]
  /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, lastApplied, leaderId,
                  nextIndex, matchIndex, electionTimeoutRand, Members, Voting,
                  snapshotLastIndex, snapshotLastTerm, snapshotInProgress, msgs, votesReceived, prevotesReceived >>

AdvanceTermOnHigherMsg(n) ==
  /\ \E m \in msgs :
       /\ m.to = n
       /\ m.type \in {"AE","RV","AER","RVR"}
       /\ m.term > currentTerm[n]
       /\ currentTerm' = [currentTerm EXCEPT ![n] = m.term]
       /\ state' = [state EXCEPT ![n] = "FOLLOWER"]
       /\ votedFor' = [votedFor EXCEPT ![n] = Null]
       /\ msgs' = msgs
  /\ UNCHANGED << log, commitIndex, lastApplied, leaderId, nextIndex, matchIndex,
                  electionTimeoutRand, timeoutElapsed, Members, Voting,
                  snapshotLastIndex, snapshotLastTerm, snapshotInProgress, votesReceived, prevotesReceived >>

Next ==
  \/ \E n \in Nodes : BecomeFollower(n)
  \/ \E n \in Nodes : BecomePreCandidate(n)
  \/ \E n \in Nodes : BecomeCandidate(n)
  \/ \E n \in Nodes : BecomeLeader(n)
  \/ \E n \in Nodes : ElectionStart(n)
  \/ \E l \in Nodes, m \in Nodes : SendAppendEntries(l, m)
  \/ \E l \in Nodes : SendHeartbeat(l)
  \/ \E n \in Nodes : RecvRequestVote(n)
  \/ \E n \in Nodes : RecvRequestVoteResponse(n)
  \/ \E n \in Nodes : PromoteAfterPrevote(n)
  \/ \E n \in Nodes : PromoteAfterVote(n)
  \/ \E n \in Nodes : RecvAppendEntries(n)
  \/ \E n \in Nodes : RecvAppendEntriesResponse(n)
  \/ \E l \in Nodes : LogCommit(l)
  \/ \E l \in Nodes : LogAppend(l)
  \/ \E n \in Nodes : LogDelete(n)
  \/ \E n \in Nodes : ApplyConfigChange(n)
  \/ \E n \in Nodes : AddNode(n)
  \/ \E n \in Nodes : RemoveNode(n)
  \/ \E n \in Nodes : SnapshotBegin(n)
  \/ \E n \in Nodes : SnapshotEnd(n)
  \/ \E n \in Nodes : ElectionTimeout(n)
  \/ \E n \in Nodes : PeriodicElectionTimeout(n)
  \/ \E n \in Nodes : PeriodicHeartbeat(n)
  \/ \E n \in Nodes : AdvanceTermOnHigherMsg(n)

Spec ==
  Init /\ [][Next]_Vars

====