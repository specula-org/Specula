---- MODULE redisraft ----

EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Servers, MaxTerm, MaxLogLen

VARIABLES
    currentTerm,
    state,
    votedFor,
    log,
    commitIndex,
    lastApplied,
    nextIndex,
    matchIndex,
    electionTimeout,
    heartbeatTimeout,
    messages,
    snapshotLastIndex,
    snapshotLastTerm,
    votingConfigChangeIndex

vars == <<currentTerm, state, votedFor, log, commitIndex, lastApplied, 
          nextIndex, matchIndex, electionTimeout, heartbeatTimeout, 
          messages, snapshotLastIndex, snapshotLastTerm, votingConfigChangeIndex>>

States == {"FOLLOWER", "PRECANDIDATE", "CANDIDATE", "LEADER"}

MessageTypes == {"RequestVoteRequest", "RequestVoteResponse", 
                 "AppendEntriesRequest", "AppendEntriesResponse",
                 "SnapshotRequest", "SnapshotResponse"}

LogEntryTypes == {"NORMAL", "CONFIG_ADD", "CONFIG_REMOVE", "NOOP"}

Message == [type: MessageTypes, term: Nat, source: Servers, dest: Servers]

LogEntry == [term: Nat, type: LogEntryTypes, data: STRING]

Init ==
    /\ currentTerm = [s \in Servers |-> 0]
    /\ state = [s \in Servers |-> "FOLLOWER"]
    /\ votedFor = [s \in Servers |-> ""]
    /\ log = [s \in Servers |-> <<>>]
    /\ commitIndex = [s \in Servers |-> 0]
    /\ lastApplied = [s \in Servers |-> 0]
    /\ nextIndex = [s \in Servers |-> [t \in Servers |-> 1]]
    /\ matchIndex = [s \in Servers |-> [t \in Servers |-> 0]]
    /\ electionTimeout = [s \in Servers |-> TRUE]
    /\ heartbeatTimeout = [s \in Servers |-> FALSE]
    /\ messages = {}
    /\ snapshotLastIndex = [s \in Servers |-> 0]
    /\ snapshotLastTerm = [s \in Servers |-> 0]
    /\ votingConfigChangeIndex = [s \in Servers |-> -1]

GetLastLogIndex(s) == 
    IF log[s] = <<>> THEN snapshotLastIndex[s]
    ELSE snapshotLastIndex[s] + Len(log[s])

GetLastLogTerm(s) ==
    IF log[s] = <<>> THEN snapshotLastTerm[s]
    ELSE log[s][Len(log[s])].term

GetLogTerm(s, index) ==
    IF index = 0 THEN 0
    ELSE IF index <= snapshotLastIndex[s] THEN snapshotLastTerm[s]
    ELSE log[s][index - snapshotLastIndex[s]].term

IsLogUpToDate(s, candidateLastLogIndex, candidateLastLogTerm) ==
    LET lastLogTerm == GetLastLogTerm(s)
        lastLogIndex == GetLastLogIndex(s)
    IN \/ candidateLastLogTerm > lastLogTerm
       \/ /\ candidateLastLogTerm = lastLogTerm
          /\ candidateLastLogIndex >= lastLogIndex

Quorum == {S \in SUBSET Servers : Cardinality(S) * 2 > Cardinality(Servers)}

BecomeFollower(s, term) ==
    /\ currentTerm' = [currentTerm EXCEPT ![s] = term]
    /\ state' = [state EXCEPT ![s] = "FOLLOWER"]
    /\ votedFor' = [votedFor EXCEPT ![s] = ""]
    /\ electionTimeout' = [electionTimeout EXCEPT ![s] = TRUE]
    /\ heartbeatTimeout' = [heartbeatTimeout EXCEPT ![s] = FALSE]
    /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex, 
                   messages, snapshotLastIndex, snapshotLastTerm, votingConfigChangeIndex>>

BecomePreCandidate(s) ==
    /\ state[s] = "FOLLOWER"
    /\ electionTimeout[s] = TRUE
    /\ state' = [state EXCEPT ![s] = "PRECANDIDATE"]
    /\ electionTimeout' = [electionTimeout EXCEPT ![s] = FALSE]
    /\ LET requestVoteMsg == [type |-> "RequestVoteRequest",
                              term |-> currentTerm[s] + 1,
                              source |-> s,
                              dest |-> t,
                              candidateId |-> s,
                              lastLogIndex |-> GetLastLogIndex(s),
                              lastLogTerm |-> GetLastLogTerm(s),
                              prevote |-> TRUE]
       IN messages' = messages \cup {requestVoteMsg : t \in Servers \ {s}}
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, lastApplied, 
                   nextIndex, matchIndex, heartbeatTimeout, snapshotLastIndex, 
                   snapshotLastTerm, votingConfigChangeIndex>>

BecomeCandidate(s) ==
    /\ \/ /\ state[s] = "FOLLOWER"
          /\ electionTimeout[s] = TRUE
       \/ state[s] = "PRECANDIDATE"
    /\ currentTerm[s] < MaxTerm
    /\ currentTerm' = [currentTerm EXCEPT ![s] = currentTerm[s] + 1]
    /\ state' = [state EXCEPT ![s] = "CANDIDATE"]
    /\ votedFor' = [votedFor EXCEPT ![s] = s]
    /\ electionTimeout' = [electionTimeout EXCEPT ![s] = FALSE]
    /\ LET requestVoteMsg == [type |-> "RequestVoteRequest",
                              term |-> currentTerm[s] + 1,
                              source |-> s,
                              dest |-> t,
                              candidateId |-> s,
                              lastLogIndex |-> GetLastLogIndex(s),
                              lastLogTerm |-> GetLastLogTerm(s),
                              prevote |-> FALSE]
       IN messages' = messages \cup {requestVoteMsg : t \in Servers \ {s}}
    /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex, 
                   heartbeatTimeout, snapshotLastIndex, snapshotLastTerm, 
                   votingConfigChangeIndex>>

BecomeLeader(s) ==
    /\ state[s] = "CANDIDATE"
    /\ LET votes == {t \in Servers : \E m \in messages : 
                        /\ m.type = "RequestVoteResponse"
                        /\ m.dest = s
                        /\ m.source = t
                        /\ m.term = currentTerm[s]
                        /\ m.voteGranted = TRUE
                        /\ m.prevote = FALSE}
           selfVote == {s}
           allVotes == votes \cup selfVote
       IN /\ allVotes \in Quorum
    /\ state' = [state EXCEPT ![s] = "LEADER"]
    /\ nextIndex' = [nextIndex EXCEPT ![s] = [t \in Servers |-> GetLastLogIndex(s) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![s] = [t \in Servers |-> 0]]
    /\ heartbeatTimeout' = [heartbeatTimeout EXCEPT ![s] = TRUE]
    /\ electionTimeout' = [electionTimeout EXCEPT ![s] = FALSE]
    /\ LET noopEntry == [term |-> currentTerm[s], type |-> "NOOP", data |-> ""]
       IN log' = [log EXCEPT ![s] = Append(log[s], noopEntry)]
    /\ UNCHANGED <<currentTerm, votedFor, commitIndex, lastApplied, messages, 
                   snapshotLastIndex, snapshotLastTerm, votingConfigChangeIndex>>

ElectionTimeout(s) ==
    /\ state[s] = "FOLLOWER"
    /\ electionTimeout[s] = FALSE
    /\ electionTimeout' = [electionTimeout EXCEPT ![s] = TRUE]
    /\ UNCHANGED <<currentTerm, state, votedFor, log, commitIndex, lastApplied, 
                   nextIndex, matchIndex, heartbeatTimeout, messages, 
                   snapshotLastIndex, snapshotLastTerm, votingConfigChangeIndex>>

HeartbeatTimeout(s) ==
    /\ state[s] = "LEADER"
    /\ heartbeatTimeout[s] = FALSE
    /\ heartbeatTimeout' = [heartbeatTimeout EXCEPT ![s] = TRUE]
    /\ UNCHANGED <<currentTerm, state, votedFor, log, commitIndex, lastApplied, 
                   nextIndex, matchIndex, electionTimeout, messages, 
                   snapshotLastIndex, snapshotLastTerm, votingConfigChangeIndex>>

RecvRequestVote(m) ==
    /\ m.type = "RequestVoteRequest"
    /\ LET s == m.dest
           candidate == m.source
           candidateTerm == m.term
           candidateLastLogIndex == m.lastLogIndex
           candidateLastLogTerm == m.lastLogTerm
           isPrevote == m.prevote
           
           logOk == IsLogUpToDate(s, candidateLastLogIndex, candidateLastLogTerm)
           
           grantVote == 
               /\ \/ candidateTerm > currentTerm[s]
                  \/ /\ candidateTerm = currentTerm[s]
                     /\ \/ votedFor[s] = ""
                        \/ votedFor[s] = candidate
               /\ logOk
               /\ \/ ~isPrevote
                  \/ /\ isPrevote
                     /\ electionTimeout[s] = TRUE
           
           response == [type |-> "RequestVoteResponse",
                        term |-> IF candidateTerm > currentTerm[s] 
                                 THEN candidateTerm 
                                 ELSE currentTerm[s],
                        source |-> s,
                        dest |-> candidate,
                        voteGranted |-> grantVote,
                        prevote |-> isPrevote]
                        
       IN /\ messages' = (messages \ {m}) \cup {response}
          /\ IF candidateTerm > currentTerm[s]
             THEN /\ currentTerm' = [currentTerm EXCEPT ![s] = candidateTerm]
                  /\ state' = [state EXCEPT ![s] = "FOLLOWER"]
                  /\ votedFor' = [votedFor EXCEPT ![s] = IF grantVote THEN candidate ELSE ""]
                  /\ electionTimeout' = [electionTimeout EXCEPT ![s] = TRUE]
             ELSE /\ IF grantVote /\ ~isPrevote
                     THEN votedFor' = [votedFor EXCEPT ![s] = candidate]
                     ELSE UNCHANGED votedFor
                  /\ UNCHANGED <<currentTerm, state, electionTimeout>>
          /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex, 
                         heartbeatTimeout, snapshotLastIndex, snapshotLastTerm, 
                         votingConfigChangeIndex>>

RecvRequestVoteResponse(m) ==
    /\ m.type = "RequestVoteResponse"
    /\ LET s == m.dest
           voter == m.source
           voterTerm == m.term
           voteGranted == m.voteGranted
           isPrevote == m.prevote
           
       IN /\ messages' = messages \ {m}
          /\ IF voterTerm > currentTerm[s]
             THEN BecomeFollower(s, voterTerm)
             ELSE /\ IF /\ voteGranted
                        /\ \/ /\ state[s] = "PRECANDIDATE"
                              /\ isPrevote
                           \/ /\ state[s] = "CANDIDATE"
                              /\ ~isPrevote
                     THEN LET votes == {t \in Servers : \E msg \in messages : 
                                          /\ msg.type = "RequestVoteResponse"
                                          /\ msg.dest = s
                                          /\ msg.source = t
                                          /\ msg.term = currentTerm[s]
                                          /\ msg.voteGranted = TRUE
                                          /\ msg.prevote = isPrevote}
                              selfVote == IF ~isPrevote THEN {s} ELSE {}
                              allVotes == votes \cup selfVote
                          IN IF allVotes \in Quorum
                             THEN IF isPrevote 
                                  THEN BecomeCandidate(s)
                                  ELSE BecomeLeader(s)
                             ELSE UNCHANGED <<currentTerm, state, votedFor, log, 
                                              commitIndex, lastApplied, nextIndex, 
                                              matchIndex, electionTimeout, heartbeatTimeout, 
                                              snapshotLastIndex, snapshotLastTerm, 
                                              votingConfigChangeIndex>>
                     ELSE UNCHANGED <<currentTerm, state, votedFor, log, commitIndex, 
                                      lastApplied, nextIndex, matchIndex, electionTimeout, 
                                      heartbeatTimeout, snapshotLastIndex, snapshotLastTerm, 
                                      votingConfigChangeIndex>>

SendAppendEntries(s, t) ==
    /\ state[s] = "LEADER"
    /\ heartbeatTimeout[s] = TRUE
    /\ LET prevLogIndex == nextIndex[s][t] - 1
           prevLogTerm == GetLogTerm(s, prevLogIndex)
           entries == IF nextIndex[s][t] <= GetLastLogIndex(s)
                      THEN SubSeq(log[s], nextIndex[s][t] - snapshotLastIndex[s], 
                                  Len(log[s]))
                      ELSE <<>>
           msg == [type |-> "AppendEntriesRequest",
                   term |-> currentTerm[s],
                   source |-> s,
                   dest |-> t,
                   prevLogIndex |-> prevLogIndex,
                   prevLogTerm |-> prevLogTerm,
                   entries |-> entries,
                   leaderCommit |-> commitIndex[s]]
       IN /\ messages' = messages \cup {msg}
          /\ heartbeatTimeout' = [heartbeatTimeout EXCEPT ![s] = FALSE]
          /\ UNCHANGED <<currentTerm, state, votedFor, log, commitIndex, 
                         lastApplied, nextIndex, matchIndex, electionTimeout, 
                         snapshotLastIndex, snapshotLastTerm, votingConfigChangeIndex>>

RecvAppendEntries(m) ==
    /\ m.type = "AppendEntriesRequest"
    /\ LET s == m.dest
           leader == m.source
           leaderTerm == m.term
           prevLogIndex == m.prevLogIndex
           prevLogTerm == m.prevLogTerm
           entries == m.entries
           leaderCommit == m.leaderCommit
           
           logOk == \/ prevLogIndex = 0
                    \/ /\ prevLogIndex <= GetLastLogIndex(s)
                       /\ GetLogTerm(s, prevLogIndex) = prevLogTerm
           
           response == [type |-> "AppendEntriesResponse",
                        term |-> IF leaderTerm > currentTerm[s] 
                                 THEN leaderTerm 
                                 ELSE currentTerm[s],
                        source |-> s,
                        dest |-> leader,
                        success |-> /\ leaderTerm >= currentTerm[s]
                                    /\ logOk,
                        matchIndex |-> IF logOk 
                                       THEN prevLogIndex + Len(entries)
                                       ELSE 0]
                                       
       IN /\ messages' = (messages \ {m}) \cup {response}
          /\ IF leaderTerm > currentTerm[s]
             THEN /\ currentTerm' = [currentTerm EXCEPT ![s] = leaderTerm]
                  /\ state' = [state EXCEPT ![s] = "FOLLOWER"]
                  /\ votedFor' = [votedFor EXCEPT ![s] = ""]
                  /\ electionTimeout' = [electionTimeout EXCEPT ![s] = TRUE]
             ELSE /\ electionTimeout' = [electionTimeout EXCEPT ![s] = TRUE]
                  /\ UNCHANGED <<currentTerm, state, votedFor>>
          /\ IF /\ leaderTerm >= currentTerm[s]
                /\ logOk
             THEN /\ LET newLog == IF entries = <<>>
                                   THEN log[s]
                                   ELSE SubSeq(log[s], 1, prevLogIndex - snapshotLastIndex[s]) 
                                        \o entries
                     IN log' = [log EXCEPT ![s] = newLog]
                  /\ commitIndex' = [commitIndex EXCEPT ![s] = 
                                       IF leaderCommit > commitIndex[s]
                                       THEN Min({leaderCommit, GetLastLogIndex(s)})
                                       ELSE commitIndex[s]]
             ELSE UNCHANGED <<log, commitIndex>>
          /\ UNCHANGED <<lastApplied, nextIndex, matchIndex, heartbeatTimeout, 
                         snapshotLastIndex, snapshotLastTerm, votingConfigChangeIndex>>

RecvAppendEntriesResponse(m) ==
    /\ m.type = "AppendEntriesResponse"
    /\ LET s == m.dest
           follower == m.source
           followerTerm == m.term
           success == m.success
           followerMatchIndex == m.matchIndex
           
       IN /\ messages' = messages \ {m}
          /\ IF followerTerm > currentTerm[s]
             THEN BecomeFollower(s, followerTerm)
             ELSE /\ IF /\ state[s] = "LEADER"
                        /\ success
                     THEN /\ matchIndex' = [matchIndex EXCEPT ![s][follower] = followerMatchIndex]
                          /\ nextIndex' = [nextIndex EXCEPT ![s][follower] = followerMatchIndex + 1]
                          /\ LET newCommitIndex == 
                                   CHOOSE index \in (commitIndex[s] + 1)..GetLastLogIndex(s) :
                                     /\ GetLogTerm(s, index) = currentTerm[s]
                                     /\ Cardinality({t \in Servers : matchIndex'[s][t] >= index}) * 2 
                                        > Cardinality(Servers)
                                     /\ \A i \in (index + 1)..GetLastLogIndex(s) :
                                          \/ GetLogTerm(s, i) # currentTerm[s]
                                          \/ Cardinality({t \in Servers : matchIndex'[s][t] >= i}) * 2 
                                             <= Cardinality(Servers)
                             IN IF \E index \in (commitIndex[s] + 1)..GetLastLogIndex(s) :
                                     /\ GetLogTerm(s, index) = currentTerm[s]
                                     /\ Cardinality({t \in Servers : matchIndex'[s][t] >= index}) * 2 
                                        > Cardinality(Servers)
                                THEN commitIndex' = [commitIndex EXCEPT ![s] = newCommitIndex]
                                ELSE UNCHANGED commitIndex
                     ELSE /\ IF /\ state[s] = "LEADER"
                              /\ ~success
                           THEN nextIndex' = [nextIndex EXCEPT ![s][follower] = 
                                                Max({1, nextIndex[s][follower] - 1})]
                           ELSE UNCHANGED nextIndex
                          /\ UNCHANGED <<matchIndex, commitIndex>>
                  /\ UNCHANGED <<currentTerm, state, votedFor, log, lastApplied, 
                                 electionTimeout, heartbeatTimeout, snapshotLastIndex, 
                                 snapshotLastTerm, votingConfigChangeIndex>>

ApplyEntry(s) ==
    /\ lastApplied[s] < commitIndex[s]
    /\ lastApplied[s] + 1 <= GetLastLogIndex(s)
    /\ LET index == lastApplied[s] + 1
           entry == log[s][index - snapshotLastIndex[s]]
       IN /\ lastApplied' = [lastApplied EXCEPT ![s] = index]
          /\ IF entry.type \in {"CONFIG_ADD", "CONFIG_REMOVE"}
             THEN IF votingConfigChangeIndex[s] = index
                  THEN votingConfigChangeIndex' = [votingConfigChangeIndex EXCEPT ![s] = -1]
                  ELSE UNCHANGED votingConfigChangeIndex
             ELSE UNCHANGED votingConfigChangeIndex
          /\ UNCHANGED <<currentTerm, state, votedFor, log, commitIndex, 
                         nextIndex, matchIndex, electionTimeout, heartbeatTimeout, 
                         messages, snapshotLastIndex, snapshotLastTerm>>

AppendEntry(s, entry) ==
    /\ state[s] = "LEADER"
    /\ Len(log[s]) < MaxLogLen
    /\ LET newEntry == [term |-> currentTerm[s], 
                        type |-> entry.type, 
                        data |-> entry.data]
       IN /\ log' = [log EXCEPT ![s] = Append(log[s], newEntry)]
          /\ IF entry.type \in {"CONFIG_ADD", "CONFIG_REMOVE"}
             THEN votingConfigChangeIndex' = [votingConfigChangeIndex EXCEPT ![s] = GetLastLogIndex(s) + 1]
             ELSE UNCHANGED votingConfigChangeIndex
          /\ UNCHANGED <<currentTerm, state, votedFor, commitIndex, lastApplied, 
                         nextIndex, matchIndex, electionTimeout, heartbeatTimeout, 
                         messages, snapshotLastIndex, snapshotLastTerm>>

BeginSnapshot(s) ==
    /\ lastApplied[s] > snapshotLastIndex[s]
    /\ snapshotLastIndex' = [snapshotLastIndex EXCEPT ![s] = lastApplied[s]]
    /\ snapshotLastTerm' = [snapshotLastTerm EXCEPT ![s] = 
                              IF lastApplied[s] <= snapshotLastIndex[s]
                              THEN snapshotLastTerm[s]
                              ELSE log[s][lastApplied[s] - snapshotLastIndex[s]].term]
    /\ log' = [log EXCEPT ![s] = <<>>]
    /\ UNCHANGED <<currentTerm, state, votedFor, commitIndex, lastApplied, 
                   nextIndex, matchIndex, electionTimeout, heartbeatTimeout, 
                   messages, votingConfigChangeIndex>>

Next ==
    \/ \E s \in Servers : 
        \/ BecomePreCandidate(s)
        \/ BecomeCandidate(s)
        \/ BecomeLeader(s)
        \/ ElectionTimeout(s)
        \/ HeartbeatTimeout(s)
        \/ ApplyEntry(s)
        \/ BeginSnapshot(s)
        \/ \E entry \in [type: LogEntryTypes, data: STRING] : AppendEntry(s, entry)
        \/ \E t \in Servers \ {s} : SendAppendEntries(s, t)
    \/ \E m \in messages :
        \/ RecvRequestVote(m)
        \/ RecvRequestVoteResponse(m)
        \/ RecvAppendEntries(m)
        \/ RecvAppendEntriesResponse(m)

Spec == Init /\ [][Next]_vars

====