---- MODULE Raft ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS 
    Server,
    Value,
    Nil,
    NoLimit

VARIABLES
    currentTerm,
    votedFor,
    log,
    commitIndex,
    state,
    leaderId,
    nextIndex,
    matchIndex,
    votesGranted,
    votesRejected,
    electionElapsed,
    heartbeatElapsed,
    randomizedElectionTimeout,
    messages,
    readStates,
    pendingReadIndexMessages,
    leadTransferee,
    pendingConfIndex,
    uncommittedSize,
    isLearner,
    config,
    readOnlyOption

vars == <<currentTerm, votedFor, log, commitIndex, state, leaderId, nextIndex, 
          matchIndex, votesGranted, votesRejected, electionElapsed, heartbeatElapsed,
          randomizedElectionTimeout, messages, readStates, pendingReadIndexMessages,
          leadTransferee, pendingConfIndex, uncommittedSize, isLearner, config,
          readOnlyOption>>

TypeInvariant ==
    /\ currentTerm \in [Server -> Nat]
    /\ votedFor \in [Server -> Server \cup {Nil}]
    /\ log \in [Server -> Seq([term: Nat, index: Nat, value: Value, type: STRING])]
    /\ commitIndex \in [Server -> Nat]
    /\ state \in [Server -> {"Follower", "Candidate", "Leader", "PreCandidate"}]
    /\ leaderId \in [Server -> Server \cup {Nil}]
    /\ nextIndex \in [Server -> [Server -> Nat]]
    /\ matchIndex \in [Server -> [Server -> Nat]]
    /\ votesGranted \in [Server -> SUBSET Server]
    /\ votesRejected \in [Server -> SUBSET Server]
    /\ electionElapsed \in [Server -> Nat]
    /\ heartbeatElapsed \in [Server -> Nat]
    /\ randomizedElectionTimeout \in [Server -> Nat]
    /\ readStates \in [Server -> Seq([index: Nat, requestCtx: STRING])]
    /\ pendingReadIndexMessages \in [Server -> Seq([from: Server, to: Server, type: STRING, entries: Seq([data: STRING])])]
    /\ leadTransferee \in [Server -> Server \cup {Nil}]
    /\ pendingConfIndex \in [Server -> Nat]
    /\ uncommittedSize \in [Server -> Nat]
    /\ isLearner \in [Server -> BOOLEAN]
    /\ config \in [Server -> [voters: SUBSET Server, learners: SUBSET Server]]
    /\ readOnlyOption \in [Server -> {"Safe", "LeaseBased"}]

Init ==
    /\ currentTerm = [s \in Server |-> 0]
    /\ votedFor = [s \in Server |-> Nil]
    /\ log = [s \in Server |-> <<>>]
    /\ commitIndex = [s \in Server |-> 0]
    /\ state = [s \in Server |-> "Follower"]
    /\ leaderId = [s \in Server |-> Nil]
    /\ nextIndex = [s \in Server |-> [t \in Server |-> 1]]
    /\ matchIndex = [s \in Server |-> [t \in Server |-> 0]]
    /\ votesGranted = [s \in Server |-> {}]
    /\ votesRejected = [s \in Server |-> {}]
    /\ electionElapsed = [s \in Server |-> 0]
    /\ heartbeatElapsed = [s \in Server |-> 0]
    /\ randomizedElectionTimeout = [s \in Server |-> 10]
    /\ messages = {}
    /\ readStates = [s \in Server |-> <<>>]
    /\ pendingReadIndexMessages = [s \in Server |-> <<>>]
    /\ leadTransferee = [s \in Server |-> Nil]
    /\ pendingConfIndex = [s \in Server |-> 0]
    /\ uncommittedSize = [s \in Server |-> 0]
    /\ isLearner = [s \in Server |-> FALSE]
    /\ config = [s \in Server |-> [voters: Server, learners: {}]]
    /\ readOnlyOption = [s \in Server |-> "Safe"]


Min(S) == CHOOSE x \in S : \A y \in S : x <= y

Max(S) == CHOOSE x \in S : \A y \in S : x >= y


becomeFollower(s, term, leader) ==
    /\ state' = [state EXCEPT ![s] = "Follower"]
    /\ currentTerm' = [currentTerm EXCEPT ![s] = term]
    /\ votedFor' = [votedFor EXCEPT ![s] = Nil]
    /\ leaderId' = [leaderId EXCEPT ![s] = leader]
    /\ electionElapsed' = [electionElapsed EXCEPT ![s] = 0]
    /\ heartbeatElapsed' = [heartbeatElapsed EXCEPT ![s] = 0]
    /\ randomizedElectionTimeout' = [randomizedElectionTimeout EXCEPT ![s] = (10 + (s * 3)) % 10]
    /\ leadTransferee' = [leadTransferee EXCEPT ![s] = Nil]
    /\ votesGranted' = [votesGranted EXCEPT ![s] = {}]
    /\ votesRejected' = [votesRejected EXCEPT ![s] = {}]
    /\ pendingConfIndex' = [pendingConfIndex EXCEPT ![s] = 0]
    /\ uncommittedSize' = [uncommittedSize EXCEPT ![s] = 0]
    /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex, messages, readStates, 
                   pendingReadIndexMessages, isLearner, config, readOnlyOption>>

becomeCandidate(s) ==
    /\ state[s] # "Leader"
    /\ state' = [state EXCEPT ![s] = "Candidate"]
    /\ currentTerm' = [currentTerm EXCEPT ![s] = currentTerm[s] + 1]
    /\ votedFor' = [votedFor EXCEPT ![s] = s]
    /\ leaderId' = [leaderId EXCEPT ![s] = Nil]
    /\ electionElapsed' = [electionElapsed EXCEPT ![s] = 0]
    /\ heartbeatElapsed' = [heartbeatElapsed EXCEPT ![s] = 0]
    /\ randomizedElectionTimeout' = [randomizedElectionTimeout EXCEPT ![s] = (10 + (s * 3)) % 10]
    /\ leadTransferee' = [leadTransferee EXCEPT ![s] = Nil]
    /\ votesGranted' = [votesGranted EXCEPT ![s] = {}]
    /\ votesRejected' = [votesRejected EXCEPT ![s] = {}]
    /\ pendingConfIndex' = [pendingConfIndex EXCEPT ![s] = 0]
    /\ uncommittedSize' = [uncommittedSize EXCEPT ![s] = 0]
    /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex, messages, readStates,
                   pendingReadIndexMessages, isLearner, config, readOnlyOption>>

becomePreCandidate(s) ==
    /\ state[s] # "Leader"
    /\ state' = [state EXCEPT ![s] = "PreCandidate"]
    /\ votesGranted' = [votesGranted EXCEPT ![s] = {}]
    /\ votesRejected' = [votesRejected EXCEPT ![s] = {}]
    /\ leaderId' = [leaderId EXCEPT ![s] = Nil]
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, electionElapsed, heartbeatElapsed,
                   randomizedElectionTimeout, nextIndex, matchIndex, messages, readStates,
                   pendingReadIndexMessages, leadTransferee, pendingConfIndex, uncommittedSize,
                   isLearner, config, readOnlyOption>>

becomeLeader(s) ==
    /\ state[s] # "Follower"
    /\ state' = [state EXCEPT ![s] = "Leader"]
    /\ leaderId' = [leaderId EXCEPT ![s] = s]
    /\ electionElapsed' = [electionElapsed EXCEPT ![s] = 0]
    /\ heartbeatElapsed' = [heartbeatElapsed EXCEPT ![s] = 0]
    /\ leadTransferee' = [leadTransferee EXCEPT ![s] = Nil]
    /\ votesGranted' = [votesGranted EXCEPT ![s] = {}]
    /\ votesRejected' = [votesRejected EXCEPT ![s] = {}]
    /\ pendingConfIndex' = [pendingConfIndex EXCEPT ![s] = Len(log[s])]
    /\ uncommittedSize' = [uncommittedSize EXCEPT ![s] = 0]
    /\ nextIndex' = [nextIndex EXCEPT ![s] = [t \in Server |-> Len(log[s]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![s] = [t \in Server |-> IF t = s THEN Len(log[s]) ELSE 0]]
    /\ log' = [log EXCEPT ![s] = Append(log[s], [term |-> currentTerm[s], 
                                                  index |-> Len(log[s]) + 1,
                                                  value |-> Nil,
                                                  type |-> "Normal"])]
    /\ messages' = messages \cup {[from |-> s, to |-> s, type |-> "AppResp", 
                                   term |-> currentTerm[s], index |-> Len(log'[s])]}
    /\ UNCHANGED <<currentTerm, votedFor, commitIndex, randomizedElectionTimeout,
                   readStates, pendingReadIndexMessages, isLearner, config, readOnlyOption>>

tickElection(s) ==
    /\ electionElapsed' = [electionElapsed EXCEPT ![s] = electionElapsed[s] + 1]
    /\ IF /\ s \in config[s].voters
          /\ ~isLearner[s]
          /\ electionElapsed'[s] >= randomizedElectionTimeout[s]
       THEN /\ electionElapsed' = [electionElapsed' EXCEPT ![s] = 0]
            /\ messages' = messages \cup {[from |-> s, to |-> s, type |-> "Hup"]}
       ELSE UNCHANGED messages
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, state, leaderId, nextIndex,
                   matchIndex, votesGranted, votesRejected, heartbeatElapsed,
                   randomizedElectionTimeout, readStates, pendingReadIndexMessages,
                   leadTransferee, pendingConfIndex, uncommittedSize, isLearner,
                   config, readOnlyOption>>

tickHeartbeat(s) ==
    /\ heartbeatElapsed' = [heartbeatElapsed EXCEPT ![s] = heartbeatElapsed[s] + 1]
    /\ electionElapsed' = [electionElapsed EXCEPT ![s] = electionElapsed[s] + 1]
    /\ IF electionElapsed'[s] >= 10
       THEN /\ electionElapsed' = [electionElapsed' EXCEPT ![s] = 0]
            /\ messages' = messages \cup {[from |-> s, to |-> s, type |-> "CheckQuorum"]}
            /\ IF state[s] = "Leader" /\ leadTransferee[s] # Nil
               THEN leadTransferee' = [leadTransferee EXCEPT ![s] = Nil]
               ELSE UNCHANGED leadTransferee
       ELSE /\ UNCHANGED <<messages, leadTransferee>>
    /\ IF state[s] = "Leader"
       THEN IF heartbeatElapsed'[s] >= 1
            THEN /\ heartbeatElapsed' = [heartbeatElapsed' EXCEPT ![s] = 0]
                 /\ messages' = messages \cup {[from |-> s, to |-> s, type |-> "Beat"]}
            ELSE UNCHANGED <<>>
       ELSE UNCHANGED <<>>
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, state, leaderId, nextIndex,
                   matchIndex, votesGranted, votesRejected, randomizedElectionTimeout,
                   readStates, pendingReadIndexMessages, pendingConfIndex, uncommittedSize,
                   isLearner, config, readOnlyOption>>

sendAppend(s, to) ==
    /\ state[s] = "Leader"
    /\ to # s
    /\ LET prevIndex == nextIndex[s][to] - 1
           prevTerm == IF prevIndex > 0 /\ prevIndex <= Len(log[s])
                       THEN log[s][prevIndex].term
                       ELSE 0
           entries == IF prevIndex >= 0 /\ prevIndex < Len(log[s])
                      THEN SubSeq(log[s], prevIndex + 1, Len(log[s]))
                      ELSE <<>>
       IN messages' = messages \cup {[from |-> s, to |-> to, type |-> "App",
                                      term |-> currentTerm[s], index |-> prevIndex,
                                      logTerm |-> prevTerm, entries |-> entries,
                                      commit |-> commitIndex[s]]}
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, state, leaderId, nextIndex,
                   matchIndex, votesGranted, votesRejected, electionElapsed, heartbeatElapsed,
                   randomizedElectionTimeout, readStates, pendingReadIndexMessages,
                   leadTransferee, pendingConfIndex, uncommittedSize, isLearner,
                   config, readOnlyOption>>

sendHeartbeat(s, to) ==
    /\ state[s] = "Leader"
    /\ to # s
    /\ LET commit == Min({matchIndex[s][to], commitIndex[s]})
       IN messages' = messages \cup {[from |-> s, to |-> to, type |-> "Heartbeat",
                                      term |-> currentTerm[s], commit |-> commit,
                                      context |-> ""]}
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, state, leaderId, nextIndex,
                   matchIndex, votesGranted, votesRejected, electionElapsed, heartbeatElapsed,
                   randomizedElectionTimeout, readStates, pendingReadIndexMessages,
                   leadTransferee, pendingConfIndex, uncommittedSize, isLearner,
                   config, readOnlyOption>>

bcastAppend(s) ==
    /\ state[s] = "Leader"
    /\ \A to \in Server \ {s} : sendAppend(s, to)

bcastHeartbeat(s) ==
    /\ state[s] = "Leader"
    /\ \A to \in Server \ {s} : sendHeartbeat(s, to)

maybeCommit(s) ==
    /\ state[s] = "Leader"
    /\ LET newCommitIndex == CHOOSE i \in 0..Len(log[s]) :
           /\ i > commitIndex[s]
           /\ log[s][i].term = currentTerm[s]
           /\ Cardinality({t \in config[s].voters : matchIndex[s][t] >= i}) * 2 > Cardinality(config[s].voters)
           /\ \A j \in (commitIndex[s] + 1)..i : TRUE
       IN IF newCommitIndex > commitIndex[s]
          THEN commitIndex' = [commitIndex EXCEPT ![s] = newCommitIndex]
          ELSE UNCHANGED commitIndex
    /\ UNCHANGED <<currentTerm, votedFor, log, state, leaderId, nextIndex, matchIndex,
                   votesGranted, votesRejected, electionElapsed, heartbeatElapsed,
                   randomizedElectionTimeout, messages, readStates, pendingReadIndexMessages,
                   leadTransferee, pendingConfIndex, uncommittedSize, isLearner,
                   config, readOnlyOption>>

appendEntry(s, entries) ==
    /\ state[s] = "Leader"
    /\ LET lastIndex == Len(log[s])
           newEntries == [i \in 1..Len(entries) |->
                          [term |-> currentTerm[s],
                           index |-> lastIndex + i,
                           value |-> entries[i].value,
                           type |-> entries[i].type]]
           totalSize == IF Len(newEntries) > 0 THEN 1 ELSE 0
       IN IF uncommittedSize[s] > 0 /\ totalSize > 0 /\ 
             uncommittedSize[s] + totalSize > NoLimit
          THEN UNCHANGED vars
          ELSE /\ log' = [log EXCEPT ![s] = log[s] \o newEntries]
               /\ uncommittedSize' = [uncommittedSize EXCEPT ![s] = uncommittedSize[s] + totalSize]
               /\ messages' = messages \cup {[from |-> s, to |-> s, type |-> "AppResp",
                                              term |-> currentTerm[s], index |-> Len(log'[s])]}
               /\ UNCHANGED <<currentTerm, votedFor, commitIndex, state, leaderId, nextIndex,
                              matchIndex, votesGranted, votesRejected, electionElapsed,
                              heartbeatElapsed, randomizedElectionTimeout, readStates,
                              pendingReadIndexMessages, leadTransferee, pendingConfIndex,
                              isLearner, config, readOnlyOption>>


campaign(s, campaignType) ==
    /\ s \in config[s].voters
    /\ ~isLearner[s]
    /\ LET voteMsg == IF campaignType = "PreElection" THEN "PreVote" ELSE "Vote"
           term == IF campaignType = "PreElection" THEN currentTerm[s] + 1 ELSE currentTerm[s]
           lastIndex == Len(log[s])
           lastTerm == IF lastIndex > 0 THEN log[s][lastIndex].term ELSE 0
       IN /\ IF campaignType = "PreElection"
             THEN becomePreCandidate(s)
             ELSE becomeCandidate(s)
          /\ messages' = messages \cup 
             {[from |-> s, to |-> s, term |-> term, 
               type |-> IF voteMsg = "Vote" THEN "VoteResp" ELSE "PreVoteResp"]} \cup
             {[from |-> s, to |-> to, term |-> term, type |-> voteMsg,
               index |-> lastIndex, logTerm |-> lastTerm, 
               context |-> IF campaignType = "Transfer" THEN "Transfer" ELSE ""] :
               to \in config[s].voters \ {s}}
          /\ UNCHANGED <<log, commitIndex, leaderId, nextIndex, matchIndex,
                         electionElapsed, heartbeatElapsed, randomizedElectionTimeout,
                         readStates, pendingReadIndexMessages, leadTransferee,
                         pendingConfIndex, uncommittedSize, isLearner, config, readOnlyOption>>

hup(s, campaignType) ==
    /\ IF state[s] = "Leader"
       THEN UNCHANGED vars
       ELSE IF ~(s \in config[s].voters) \/ isLearner[s]
            THEN UNCHANGED vars
            ELSE campaign(s, campaignType)

poll(s, from, msgType, granted) ==
    /\ IF granted
       THEN votesGranted' = [votesGranted EXCEPT ![s] = votesGranted[s] \cup {from}]
       ELSE votesRejected' = [votesRejected EXCEPT ![s] = votesRejected[s] \cup {from}]
    /\ LET grantedCount == Cardinality(votesGranted'[s])
           rejectedCount == Cardinality(votesRejected'[s])
           voterCount == Cardinality(config[s].voters)
       IN IF grantedCount * 2 > voterCount
          THEN IF state[s] = "PreCandidate"
               THEN campaign(s, "Election")
               ELSE /\ becomeLeader(s)
                    /\ bcastAppend(s)
          ELSE IF rejectedCount * 2 >= voterCount
               THEN becomeFollower(s, currentTerm[s], Nil)
               ELSE UNCHANGED vars

stepLeader(s, m) ==
    \/ /\ m.type = "Beat"
       /\ bcastHeartbeat(s)
    \/ /\ m.type = "CheckQuorum"
       /\ LET activeCount == Cardinality({t \in config[s].voters : 
                                          t = s \/ matchIndex[s][t] > 0})
          IN IF activeCount * 2 <= Cardinality(config[s].voters)
             THEN becomeFollower(s, currentTerm[s], Nil)
             ELSE UNCHANGED vars
    \/ /\ m.type = "Prop"
       /\ m.from = s
       /\ IF s \notin config[s].voters
          THEN UNCHANGED vars
          ELSE IF leadTransferee[s] # Nil
               THEN UNCHANGED vars
               ELSE appendEntry(s, m.entries)
    \/ /\ m.type = "AppResp"
       /\ IF m.reject
          THEN /\ LET nextProbeIdx == IF m.logTerm > 0
                                      THEN m.rejectHint
                                      ELSE m.rejectHint
                  IN /\ nextIndex' = [nextIndex EXCEPT ![s][m.from] = 
                                      Max({nextProbeIdx, 1})]
                     /\ sendAppend(s, m.from)
                     /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, state,
                                    leaderId, matchIndex, votesGranted, votesRejected,
                                    electionElapsed, heartbeatElapsed, randomizedElectionTimeout,
                                    readStates, pendingReadIndexMessages, leadTransferee,
                                    pendingConfIndex, uncommittedSize, isLearner,
                                    config, readOnlyOption>>
          ELSE /\ matchIndex' = [matchIndex EXCEPT ![s][m.from] = 
                                 Max({matchIndex[s][m.from], m.index})]
               /\ nextIndex' = [nextIndex EXCEPT ![s][m.from] = m.index + 1]
               /\ IF maybeCommit(s)
                  THEN bcastAppend(s)
                  ELSE IF m.from # s
                       THEN sendAppend(s, m.from)
                       ELSE UNCHANGED messages
               /\ IF m.from = leadTransferee[s] /\ matchIndex'[s][m.from] = Len(log[s])
                  THEN messages' = messages \cup {[from |-> s, to |-> m.from, 
                                                   type |-> "TimeoutNow"]}
                  ELSE UNCHANGED <<>>
               /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, state, leaderId,
                              votesGranted, votesRejected, electionElapsed, heartbeatElapsed,
                              randomizedElectionTimeout, readStates, pendingReadIndexMessages,
                              leadTransferee, pendingConfIndex, uncommittedSize, isLearner,
                              config, readOnlyOption>>
    \/ /\ m.type = "HeartbeatResp"
       /\ matchIndex' = [matchIndex EXCEPT ![s][m.from] = matchIndex[s][m.from]]
       /\ IF matchIndex[s][m.from] < Len(log[s])
          THEN sendAppend(s, m.from)
          ELSE UNCHANGED messages
       /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, state, leaderId, nextIndex,
                      votesGranted, votesRejected, electionElapsed, heartbeatElapsed,
                      randomizedElectionTimeout, readStates, pendingReadIndexMessages,
                      leadTransferee, pendingConfIndex, uncommittedSize, isLearner,
                      config, readOnlyOption>>
    \/ /\ m.type = "TransferLeader"
       /\ IF m.from \in config[s].learners
          THEN UNCHANGED vars
          ELSE IF leadTransferee[s] # Nil
               THEN IF leadTransferee[s] = m.from
                    THEN UNCHANGED vars
                    ELSE /\ leadTransferee' = [leadTransferee EXCEPT ![s] = Nil]
                         /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, state,
                                        leaderId, nextIndex, matchIndex, votesGranted,
                                        votesRejected, electionElapsed, heartbeatElapsed,
                                        randomizedElectionTimeout, messages, readStates,
                                        pendingReadIndexMessages, pendingConfIndex,
                                        uncommittedSize, isLearner, config, readOnlyOption>>
               ELSE IF m.from = s
                    THEN UNCHANGED vars
                    ELSE /\ electionElapsed' = [electionElapsed EXCEPT ![s] = 0]
                         /\ leadTransferee' = [leadTransferee EXCEPT ![s] = m.from]
                         /\ IF matchIndex[s][m.from] = Len(log[s])
                            THEN messages' = messages \cup {[from |-> s, to |-> m.from,
                                                             type |-> "TimeoutNow"]}
                            ELSE sendAppend(s, m.from)
                         /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, state,
                                        leaderId, nextIndex, matchIndex, votesGranted,
                                        votesRejected, heartbeatElapsed, randomizedElectionTimeout,
                                        readStates, pendingReadIndexMessages, pendingConfIndex,
                                        uncommittedSize, isLearner, config, readOnlyOption>>

handleAppendEntries(s, m) ==
    /\ IF m.index < commitIndex[s]
       THEN messages' = messages \cup {[from |-> s, to |-> m.from, type |-> "AppResp",
                                        term |-> currentTerm[s], index |-> commitIndex[s]]}
       ELSE LET prevIndex == m.index
                prevTerm == m.logTerm
                logOk == \/ prevIndex = 0
                         \/ /\ prevIndex <= Len(log[s])
                            /\ log[s][prevIndex].term = prevTerm
            IN IF logOk
               THEN /\ log' = [log EXCEPT ![s] = SubSeq(log[s], 1, prevIndex) \o m.entries]
                    /\ commitIndex' = [commitIndex EXCEPT ![s] = 
                                       Min({m.commit, prevIndex + Len(m.entries)})]
                    /\ messages' = messages \cup {[from |-> s, to |-> m.from, type |-> "AppResp",
                                                   term |-> currentTerm[s], 
                                                   index |-> prevIndex + Len(m.entries)]}
               ELSE LET hintIndex == Min({m.index, Len(log[s])})
                        hintTerm == IF hintIndex > 0 /\ hintIndex <= Len(log[s])
                                    THEN log[s][hintIndex].term
                                    ELSE 0
                    IN messages' = messages \cup {[from |-> s, to |-> m.from, type |-> "AppResp",
                                                   term |-> currentTerm[s], index |-> m.index,
                                                   reject |-> TRUE, rejectHint |-> hintIndex,
                                                   logTerm |-> hintTerm]}
    /\ UNCHANGED <<currentTerm, votedFor, state, leaderId, nextIndex, matchIndex,
                   votesGranted, votesRejected, electionElapsed, heartbeatElapsed,
                   randomizedElectionTimeout, readStates, pendingReadIndexMessages,
                   leadTransferee, pendingConfIndex, uncommittedSize, isLearner,
                   config, readOnlyOption>>

handleHeartbeat(s, m) ==
    /\ commitIndex' = [commitIndex EXCEPT ![s] = Max({commitIndex[s], m.commit})]
    /\ messages' = messages \cup {[from |-> s, to |-> m.from, type |-> "HeartbeatResp",
                                   term |-> currentTerm[s], context |-> m.context]}
    /\ UNCHANGED <<currentTerm, votedFor, log, state, leaderId, nextIndex, matchIndex,
                   votesGranted, votesRejected, electionElapsed, heartbeatElapsed,
                   randomizedElectionTimeout, readStates, pendingReadIndexMessages,
                   leadTransferee, pendingConfIndex, uncommittedSize, isLearner,
                   config, readOnlyOption>>

handleSnapshot(s, m) ==
    /\ LET snap == m.snapshot
           snapIndex == snap.metadata.index
           snapTerm == snap.metadata.term
       IN IF snapIndex <= commitIndex[s]
          THEN messages' = messages \cup {[from |-> s, to |-> m.from, type |-> "AppResp",
                                           term |-> currentTerm[s], index |-> commitIndex[s]]}
          ELSE /\ log' = [log EXCEPT ![s] = <<>>]
               /\ commitIndex' = [commitIndex EXCEPT ![s] = snapIndex]
               /\ messages' = messages \cup {[from |-> s, to |-> m.from, type |-> "AppResp",
                                             term |-> currentTerm[s], index |-> snapIndex]}
    /\ UNCHANGED <<currentTerm, votedFor, state, leaderId, nextIndex, matchIndex,
                   votesGranted, votesRejected, electionElapsed, heartbeatElapsed,
                   randomizedElectionTimeout, readStates, pendingReadIndexMessages,
                   leadTransferee, pendingConfIndex, uncommittedSize, isLearner,
                   config, readOnlyOption>>




stepCandidate(s, m) ==
    LET myVoteRespType == IF state[s] = "PreCandidate" THEN "PreVoteResp" ELSE "VoteResp"
    IN \/ /\ m.type = "Prop"
          /\ UNCHANGED vars
       \/ /\ m.type = "App"
          /\ becomeFollower(s, m.term, m.from)
          /\ handleAppendEntries(s, m)
       \/ /\ m.type = "Heartbeat"
          /\ becomeFollower(s, m.term, m.from)
          /\ handleHeartbeat(s, m)
       \/ /\ m.type = "Snap"
          /\ becomeFollower(s, m.term, m.from)
          /\ handleSnapshot(s, m)
       \/ /\ m.type = myVoteRespType
          /\ poll(s, m.from, m.type, ~m.reject)
       \/ /\ m.type = "TimeoutNow"
          /\ UNCHANGED vars

stepFollower(s, m) ==
    \/ /\ m.type = "Prop"
       /\ IF leaderId[s] = Nil
          THEN UNCHANGED vars
          ELSE messages' = messages \cup {[from |-> s, to |-> leaderId[s],
                                           type |-> m.type, entries |-> m.entries]}
       /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, state, leaderId,
                      nextIndex, matchIndex, votesGranted, votesRejected, electionElapsed,
                      heartbeatElapsed, randomizedElectionTimeout, readStates,
                      pendingReadIndexMessages, leadTransferee, pendingConfIndex,
                      uncommittedSize, isLearner, config, readOnlyOption>>
    \/ /\ m.type = "App"
       /\ electionElapsed' = [electionElapsed EXCEPT ![s] = 0]
       /\ leaderId' = [leaderId EXCEPT ![s] = m.from]
       /\ handleAppendEntries(s, m)
    \/ /\ m.type = "Heartbeat"
       /\ electionElapsed' = [electionElapsed EXCEPT ![s] = 0]
       /\ leaderId' = [leaderId EXCEPT ![s] = m.from]
       /\ handleHeartbeat(s, m)
    \/ /\ m.type = "Snap"
       /\ electionElapsed' = [electionElapsed EXCEPT ![s] = 0]
       /\ leaderId' = [leaderId EXCEPT ![s] = m.from]
       /\ handleSnapshot(s, m)
    \/ /\ m.type = "TransferLeader"
       /\ IF leaderId[s] = Nil
          THEN UNCHANGED vars
          ELSE messages' = messages \cup {[from |-> s, to |-> leaderId[s],
                                           type |-> m.type]}
       /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, state, leaderId,
                      nextIndex, matchIndex, votesGranted, votesRejected, electionElapsed,
                      heartbeatElapsed, randomizedElectionTimeout, readStates,
                      pendingReadIndexMessages, leadTransferee, pendingConfIndex,
                      uncommittedSize, isLearner, config, readOnlyOption>>
    \/ /\ m.type = "TimeoutNow"
       /\ hup(s, "Transfer")
    \/ /\ m.type = "ReadIndex"
       /\ IF leaderId[s] = Nil
          THEN UNCHANGED vars
          ELSE messages' = messages \cup {[from |-> s, to |-> leaderId[s],
                                           type |-> m.type, entries |-> m.entries]}
       /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, state, leaderId,
                      nextIndex, matchIndex, votesGranted, votesRejected, electionElapsed,
                      heartbeatElapsed, randomizedElectionTimeout, readStates,
                      pendingReadIndexMessages, leadTransferee, pendingConfIndex,
                      uncommittedSize, isLearner, config, readOnlyOption>>
    \/ /\ m.type = "ReadIndexResp"
       /\ IF Len(m.entries) = 1
          THEN readStates' = [readStates EXCEPT ![s] = 
                              Append(readStates[s], [index |-> m.index, 
                                                     requestCtx |-> m.entries[1].data])]
          ELSE UNCHANGED readStates
       /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, state, leaderId,
                      nextIndex, matchIndex, votesGranted, votesRejected, electionElapsed,
                      heartbeatElapsed, randomizedElectionTimeout, messages,
                      pendingReadIndexMessages, leadTransferee, pendingConfIndex,
                      uncommittedSize, isLearner, config, readOnlyOption>>

RECURSIVE Step(_, _)

Step(s, m) ==
    \/ /\ m.term = 0
       /\ \/ /\ m.type = "Hup"
             /\ hup(s, "Election")
          \/ /\ m.type = "StorageAppendResp"
             /\ IF m.index # 0
                THEN log' = [log EXCEPT ![s] = log[s]]
                ELSE UNCHANGED log
             /\ UNCHANGED <<currentTerm, votedFor, commitIndex, state, leaderId,
                            nextIndex, matchIndex, votesGranted, votesRejected,
                            electionElapsed, heartbeatElapsed, randomizedElectionTimeout,
                            messages, readStates, pendingReadIndexMessages, leadTransferee,
                            pendingConfIndex, uncommittedSize, isLearner, config,
                            readOnlyOption>>
          \/ /\ m.type = "StorageApplyResp"
             /\ IF Len(m.entries) > 0
                THEN /\ LET lastIndex == m.entries[Len(m.entries)].index
                            size == Len(m.entries)
                        IN /\ commitIndex' = [commitIndex EXCEPT ![s] = lastIndex]
                           /\ uncommittedSize' = [uncommittedSize EXCEPT ![s] = 
                                                  Max({0, uncommittedSize[s] - size})]
                ELSE UNCHANGED <<commitIndex, uncommittedSize>>
             /\ UNCHANGED <<currentTerm, votedFor, log, state, leaderId, nextIndex,
                            matchIndex, votesGranted, votesRejected, electionElapsed,
                            heartbeatElapsed, randomizedElectionTimeout, messages,
                            readStates, pendingReadIndexMessages, leadTransferee,
                            pendingConfIndex, isLearner, config, readOnlyOption>>
          \/ /\ m.type \in {"Vote", "PreVote"}
             /\ LET canVote == \/ votedFor[s] = m.from
                               \/ /\ votedFor[s] = Nil
                                  /\ leaderId[s] = Nil
                               \/ /\ m.type = "PreVote"
                                  /\ m.term > currentTerm[s]
                    lastIndex == Len(log[s])
                    lastTerm == IF lastIndex > 0 THEN log[s][lastIndex].term ELSE 0
                    logOk == \/ m.logTerm > lastTerm
                             \/ /\ m.logTerm = lastTerm
                                /\ m.index >= lastIndex
                IN IF canVote /\ logOk
                   THEN /\ messages' = messages \cup {[from |-> s, to |-> m.from,
                                                        term |-> m.term,
                                                        type |-> IF m.type = "Vote" 
                                                                 THEN "VoteResp" 
                                                                 ELSE "PreVoteResp"]}
                        /\ IF m.type = "Vote"
                           THEN /\ electionElapsed' = [electionElapsed EXCEPT ![s] = 0]
                                /\ votedFor' = [votedFor EXCEPT ![s] = m.from]
                           ELSE UNCHANGED <<electionElapsed, votedFor>>
                   ELSE messages' = messages \cup {[from |-> s, to |-> m.from,
                                                    term |-> currentTerm[s],
                                                    type |-> IF m.type = "Vote"
                                                             THEN "VoteResp"
                                                             ELSE "PreVoteResp",
                                                    reject |-> TRUE]}
             /\ UNCHANGED <<currentTerm, log, commitIndex, state, leaderId, nextIndex,
                            matchIndex, votesGranted, votesRejected, heartbeatElapsed,
                            randomizedElectionTimeout, readStates, pendingReadIndexMessages,
                            leadTransferee, pendingConfIndex, uncommittedSize, isLearner,
                            config, readOnlyOption>>
          \/ /\ state[s] = "Leader"
             /\ stepLeader(s, m)
          \/ /\ state[s] \in {"Candidate", "PreCandidate"}
             /\ stepCandidate(s, m)
          \/ /\ state[s] = "Follower"
             /\ stepFollower(s, m)
    \/ /\ m.term > currentTerm[s]
       /\ IF m.type \in {"Vote", "PreVote"}
          THEN /\ LET force == m.context = "Transfer"
                      inLease == leaderId[s] # Nil /\ 
                                 electionElapsed[s] < randomizedElectionTimeout[s]
                  IN IF ~force /\ inLease
                     THEN UNCHANGED vars
                     ELSE Step(s, [m EXCEPT !.term = 0])
          ELSE IF m.type = "PreVote"
               THEN UNCHANGED vars
               ELSE IF m.type = "PreVoteResp" /\ ~m.reject
                    THEN UNCHANGED vars
                    ELSE /\ IF m.type \in {"App", "Heartbeat", "Snap"}
                            THEN becomeFollower(s, m.term, m.from)
                            ELSE becomeFollower(s, m.term, Nil)
                         /\ Step(s, [m EXCEPT !.term = 0])
    \/ /\ m.term < currentTerm[s]
       /\ IF m.type \in {"Heartbeat", "App"}
          THEN messages' = messages \cup {[from |-> s, to |-> m.from,
                                           type |-> "AppResp", term |-> currentTerm[s]]}
          ELSE IF m.type = "PreVote"
               THEN messages' = messages \cup {[from |-> s, to |-> m.from,
                                                term |-> currentTerm[s],
                                                type |-> "PreVoteResp",
                                                reject |-> TRUE]}
               ELSE IF m.type = "StorageAppendResp"
                    THEN IF m.snapshot # Nil
                         THEN commitIndex' = [commitIndex EXCEPT ![s] = 
                                              m.snapshot.metadata.index]
                         ELSE UNCHANGED commitIndex
                    ELSE UNCHANGED messages
       /\ UNCHANGED <<currentTerm, votedFor, log, state, leaderId, nextIndex,
                      matchIndex, votesGranted, votesRejected, electionElapsed,
                      heartbeatElapsed, randomizedElectionTimeout, readStates,
                      pendingReadIndexMessages, leadTransferee, pendingConfIndex,
                      uncommittedSize, isLearner, config, readOnlyOption>>


Next ==
    \/ \E s \in Server : tickElection(s)
    \/ \E s \in Server : tickHeartbeat(s)
    \/ \E s \in Server : \E m \in messages : Step(s, m)

Spec == Init /\ [][Next]_vars

TypeOK == TypeInvariant

====