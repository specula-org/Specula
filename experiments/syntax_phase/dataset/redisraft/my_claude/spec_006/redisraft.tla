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
    votesGranted,
    snapshotLastIndex,
    snapshotLastTerm,
    configChangeInProgress,
    activeNodes

vars == <<currentTerm, state, votedFor, log, commitIndex, lastApplied,
          nextIndex, matchIndex, electionTimeout, heartbeatTimeout,
          messages, votesGranted, snapshotLastIndex, snapshotLastTerm,
          configChangeInProgress, activeNodes>>

States == {"FOLLOWER", "PRECANDIDATE", "CANDIDATE", "LEADER"}
LogEntryTypes == {"NORMAL", "CONFIG_ADD", "CONFIG_REMOVE", "NOOP"}

Message == [type: {"RequestVote", "RequestVoteResponse", "AppendEntries", 
                   "AppendEntriesResponse", "Snapshot", "SnapshotResponse"},
            term: Nat,
            source: Servers,
            dest: Servers]

LogEntry == [term: Nat, type: LogEntryTypes, data: Nat]

TypeOK ==
    /\ currentTerm \in [Servers -> Nat]
    /\ state \in [Servers -> States]
    /\ votedFor \in [Servers -> Servers \cup {Nil}]
    /\ log \in [Servers -> Seq(LogEntry)]
    /\ commitIndex \in [Servers -> Nat]
    /\ lastApplied \in [Servers -> Nat]
    /\ nextIndex \in [Servers -> [Servers -> Nat]]
    /\ matchIndex \in [Servers -> [Servers -> Nat]]
    /\ electionTimeout \in [Servers -> BOOLEAN]
    /\ heartbeatTimeout \in [Servers -> BOOLEAN]
    /\ messages \subseteq Message
    /\ votesGranted \in [Servers -> SUBSET Servers]
    /\ snapshotLastIndex \in [Servers -> Nat]
    /\ snapshotLastTerm \in [Servers -> Nat]
    /\ configChangeInProgress \in [Servers -> BOOLEAN]
    /\ activeNodes \in [Servers -> SUBSET Servers]

Init ==
    /\ currentTerm = [s \in Servers |-> 0]
    /\ state = [s \in Servers |-> "FOLLOWER"]
    /\ votedFor = [s \in Servers |-> Nil]
    /\ log = [s \in Servers |-> <<>>]
    /\ commitIndex = [s \in Servers |-> 0]
    /\ lastApplied = [s \in Servers |-> 0]
    /\ nextIndex = [s \in Servers |-> [t \in Servers |-> 1]]
    /\ matchIndex = [s \in Servers |-> [t \in Servers |-> 0]]
    /\ electionTimeout = [s \in Servers |-> FALSE]
    /\ heartbeatTimeout = [s \in Servers |-> FALSE]
    /\ messages = {}
    /\ votesGranted = [s \in Servers |-> {}]
    /\ snapshotLastIndex = [s \in Servers |-> 0]
    /\ snapshotLastTerm = [s \in Servers |-> 0]
    /\ configChangeInProgress = [s \in Servers |-> FALSE]
    /\ activeNodes = [s \in Servers |-> Servers]

GetLastLogIndex(s) == 
    IF log[s] = <<>> THEN snapshotLastIndex[s]
    ELSE snapshotLastIndex[s] + Len(log[s])

GetLastLogTerm(s) ==
    IF log[s] = <<>> THEN snapshotLastTerm[s]
    ELSE log[s][Len(log[s])].term

GetLogTerm(s, i) ==
    IF i = 0 THEN 0
    ELSE IF i <= snapshotLastIndex[s] THEN snapshotLastTerm[s]
    ELSE log[s][i - snapshotLastIndex[s]].term

IsQuorum(nodes) == Cardinality(nodes) * 2 > Cardinality(Servers)

BecomeFollower(s, term) ==
    /\ currentTerm' = [currentTerm EXCEPT ![s] = term]
    /\ state' = [state EXCEPT ![s] = "FOLLOWER"]
    /\ votedFor' = [votedFor EXCEPT ![s] = Nil]
    /\ electionTimeout' = [electionTimeout EXCEPT ![s] = FALSE]
    /\ heartbeatTimeout' = [heartbeatTimeout EXCEPT ![s] = FALSE]
    /\ votesGranted' = [votesGranted EXCEPT ![s] = {}]

BecomePreCandidate(s) ==
    /\ state[s] = "FOLLOWER"
    /\ electionTimeout[s] = TRUE
    /\ state' = [state EXCEPT ![s] = "PRECANDIDATE"]
    /\ votesGranted' = [votesGranted EXCEPT ![s] = {s}]
    /\ electionTimeout' = [electionTimeout EXCEPT ![s] = FALSE]
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, lastApplied,
                   nextIndex, matchIndex, heartbeatTimeout, messages,
                   snapshotLastIndex, snapshotLastTerm, configChangeInProgress,
                   activeNodes>>

BecomeCandidate(s) ==
    /\ \/ /\ state[s] = "PRECANDIDATE"
          /\ IsQuorum(votesGranted[s])
       \/ /\ state[s] = "FOLLOWER"
          /\ electionTimeout[s] = TRUE
    /\ currentTerm[s] < MaxTerm
    /\ currentTerm' = [currentTerm EXCEPT ![s] = currentTerm[s] + 1]
    /\ state' = [state EXCEPT ![s] = "CANDIDATE"]
    /\ votedFor' = [votedFor EXCEPT ![s] = s]
    /\ votesGranted' = [votesGranted EXCEPT ![s] = {s}]
    /\ electionTimeout' = [electionTimeout EXCEPT ![s] = FALSE]
    /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex,
                   heartbeatTimeout, messages, snapshotLastIndex,
                   snapshotLastTerm, configChangeInProgress, activeNodes>>

BecomeLeader(s) ==
    /\ state[s] = "CANDIDATE"
    /\ IsQuorum(votesGranted[s])
    /\ state' = [state EXCEPT ![s] = "LEADER"]
    /\ nextIndex' = [nextIndex EXCEPT ![s] = 
                     [t \in Servers |-> GetLastLogIndex(s) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![s] = 
                      [t \in Servers |-> IF t = s THEN GetLastLogIndex(s) ELSE 0]]
    /\ heartbeatTimeout' = [heartbeatTimeout EXCEPT ![s] = TRUE]
    /\ LET noopEntry == [term |-> currentTerm[s], type |-> "NOOP", data |-> 0]
       IN /\ Len(log[s]) < MaxLogLen
          /\ log' = [log EXCEPT ![s] = Append(log[s], noopEntry)]
    /\ UNCHANGED <<currentTerm, votedFor, commitIndex, lastApplied,
                   electionTimeout, messages, votesGranted, snapshotLastIndex,
                   snapshotLastTerm, configChangeInProgress, activeNodes>>

ElectionTimeout(s) ==
    /\ state[s] = "FOLLOWER"
    /\ electionTimeout' = [electionTimeout EXCEPT ![s] = TRUE]
    /\ UNCHANGED <<currentTerm, state, votedFor, log, commitIndex, lastApplied,
                   nextIndex, matchIndex, heartbeatTimeout, messages,
                   votesGranted, snapshotLastIndex, snapshotLastTerm,
                   configChangeInProgress, activeNodes>>

HeartbeatTimeout(s) ==
    /\ state[s] = "LEADER"
    /\ heartbeatTimeout' = [heartbeatTimeout EXCEPT ![s] = TRUE]
    /\ UNCHANGED <<currentTerm, state, votedFor, log, commitIndex, lastApplied,
                   nextIndex, matchIndex, electionTimeout, messages,
                   votesGranted, snapshotLastIndex, snapshotLastTerm,
                   configChangeInProgress, activeNodes>>

SendRequestVote(s, t) ==
    /\ \/ state[s] = "PRECANDIDATE"
       \/ state[s] = "CANDIDATE"
    /\ t \in activeNodes[s]
    /\ t # s
    /\ LET msg == [type |-> "RequestVote",
                   term |-> IF state[s] = "PRECANDIDATE" 
                           THEN currentTerm[s] + 1 
                           ELSE currentTerm[s],
                   source |-> s,
                   dest |-> t,
                   lastLogIndex |-> GetLastLogIndex(s),
                   lastLogTerm |-> GetLastLogTerm(s),
                   prevote |-> state[s] = "PRECANDIDATE"]
       IN messages' = messages \cup {msg}
    /\ UNCHANGED <<currentTerm, state, votedFor, log, commitIndex, lastApplied,
                   nextIndex, matchIndex, electionTimeout, heartbeatTimeout,
                   votesGranted, snapshotLastIndex, snapshotLastTerm,
                   configChangeInProgress, activeNodes>>

RecvRequestVote(s, m) ==
    /\ m.type = "RequestVote"
    /\ m.dest = s
    /\ LET grant == /\ m.term >= currentTerm[s]
                    /\ \/ votedFor[s] = Nil
                       \/ votedFor[s] = m.source
                    /\ \/ m.lastLogTerm > GetLastLogTerm(s)
                       \/ /\ m.lastLogTerm = GetLastLogTerm(s)
                          /\ m.lastLogIndex >= GetLastLogIndex(s)
                    /\ \/ ~m.prevote
                       \/ /\ m.prevote
                          /\ \/ state[s] # "FOLLOWER"
                             \/ electionTimeout[s] = TRUE
       IN /\ IF m.term > currentTerm[s]
             THEN /\ currentTerm' = [currentTerm EXCEPT ![s] = m.term]
                  /\ state' = [state EXCEPT ![s] = "FOLLOWER"]
                  /\ votedFor' = [votedFor EXCEPT ![s] = 
                                  IF grant /\ ~m.prevote THEN m.source ELSE Nil]
             ELSE /\ IF grant /\ ~m.prevote
                     THEN votedFor' = [votedFor EXCEPT ![s] = m.source]
                     ELSE UNCHANGED votedFor
                  /\ UNCHANGED <<currentTerm, state>>
          /\ LET response == [type |-> "RequestVoteResponse",
                             term |-> currentTerm'[s],
                             source |-> s,
                             dest |-> m.source,
                             voteGranted |-> grant,
                             prevote |-> m.prevote]
             IN messages' = (messages \ {m}) \cup {response}
    /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex,
                   electionTimeout, heartbeatTimeout, votesGranted,
                   snapshotLastIndex, snapshotLastTerm, configChangeInProgress,
                   activeNodes>>

RecvRequestVoteResponse(s, m) ==
    /\ m.type = "RequestVoteResponse"
    /\ m.dest = s
    /\ IF m.term > currentTerm[s]
       THEN BecomeFollower(s, m.term)
            /\ messages' = messages \ {m}
       ELSE /\ m.term = currentTerm[s]
            /\ \/ /\ m.prevote
                  /\ state[s] = "PRECANDIDATE"
               \/ /\ ~m.prevote
                  /\ state[s] = "CANDIDATE"
            /\ IF m.voteGranted
               THEN votesGranted' = [votesGranted EXCEPT ![s] = 
                                     votesGranted[s] \cup {m.source}]
               ELSE UNCHANGED votesGranted
            /\ messages' = messages \ {m}
            /\ UNCHANGED <<currentTerm, state, votedFor, log, commitIndex,
                           lastApplied, nextIndex, matchIndex, electionTimeout,
                           heartbeatTimeout, snapshotLastIndex, snapshotLastTerm,
                           configChangeInProgress, activeNodes>>

SendAppendEntries(s, t) ==
    /\ state[s] = "LEADER"
    /\ t \in activeNodes[s]
    /\ t # s
    /\ \/ heartbeatTimeout[s] = TRUE
       \/ nextIndex[s][t] <= GetLastLogIndex(s)
    /\ LET prevLogIndex == nextIndex[s][t] - 1
           prevLogTerm == GetLogTerm(s, prevLogIndex)
           entries == IF nextIndex[s][t] <= GetLastLogIndex(s)
                     THEN SubSeq(log[s], 
                                nextIndex[s][t] - snapshotLastIndex[s],
                                Len(log[s]))
                     ELSE <<>>
           msg == [type |-> "AppendEntries",
                   term |-> currentTerm[s],
                   source |-> s,
                   dest |-> t,
                   prevLogIndex |-> prevLogIndex,
                   prevLogTerm |-> prevLogTerm,
                   entries |-> entries,
                   leaderCommit |-> commitIndex[s]]
       IN messages' = messages \cup {msg}
    /\ IF heartbeatTimeout[s] = TRUE
       THEN heartbeatTimeout' = [heartbeatTimeout EXCEPT ![s] = FALSE]
       ELSE UNCHANGED heartbeatTimeout
    /\ UNCHANGED <<currentTerm, state, votedFor, log, commitIndex, lastApplied,
                   nextIndex, matchIndex, electionTimeout, messages,
                   votesGranted, snapshotLastIndex, snapshotLastTerm,
                   configChangeInProgress, activeNodes>>

RecvAppendEntries(s, m) ==
    /\ m.type = "AppendEntries"
    /\ m.dest = s
    /\ LET success == /\ m.term >= currentTerm[s]
                      /\ \/ m.prevLogIndex = 0
                         \/ /\ m.prevLogIndex <= GetLastLogIndex(s)
                            /\ GetLogTerm(s, m.prevLogIndex) = m.prevLogTerm
       IN /\ IF m.term > currentTerm[s]
             THEN BecomeFollower(s, m.term)
             ELSE IF m.term = currentTerm[s] /\ state[s] # "FOLLOWER"
                  THEN /\ state' = [state EXCEPT ![s] = "FOLLOWER"]
                       /\ UNCHANGED <<currentTerm, votedFor>>
                  ELSE UNCHANGED <<currentTerm, state, votedFor>>
          /\ IF success /\ m.entries # <<>>
             THEN /\ log' = [log EXCEPT ![s] = 
                            SubSeq(log[s], 1, m.prevLogIndex - snapshotLastIndex[s]) 
                            \o m.entries]
                  /\ IF m.leaderCommit > commitIndex[s]
                     THEN commitIndex' = [commitIndex EXCEPT ![s] = 
                                         Min({m.leaderCommit, 
                                             GetLastLogIndex(s)})]
                     ELSE UNCHANGED commitIndex
             ELSE UNCHANGED <<log, commitIndex>>
          /\ electionTimeout' = [electionTimeout EXCEPT ![s] = FALSE]
          /\ LET response == [type |-> "AppendEntriesResponse",
                             term |-> currentTerm'[s],
                             source |-> s,
                             dest |-> m.source,
                             success |-> success,
                             matchIndex |-> IF success 
                                           THEN m.prevLogIndex + Len(m.entries)
                                           ELSE 0]
             IN messages' = (messages \ {m}) \cup {response}
    /\ UNCHANGED <<lastApplied, nextIndex, matchIndex, heartbeatTimeout,
                   votesGranted, snapshotLastIndex, snapshotLastTerm,
                   configChangeInProgress, activeNodes>>

RecvAppendEntriesResponse(s, m) ==
    /\ m.type = "AppendEntriesResponse"
    /\ m.dest = s
    /\ state[s] = "LEADER"
    /\ IF m.term > currentTerm[s]
       THEN BecomeFollower(s, m.term)
            /\ messages' = messages \ {m}
       ELSE /\ m.term = currentTerm[s]
            /\ IF m.success
               THEN /\ nextIndex' = [nextIndex EXCEPT ![s][m.source] = 
                                     m.matchIndex + 1]
                    /\ matchIndex' = [matchIndex EXCEPT ![s][m.source] = 
                                      m.matchIndex]
               ELSE /\ nextIndex' = [nextIndex EXCEPT ![s][m.source] = 
                                     Max({1, nextIndex[s][m.source] - 1})]
                    /\ UNCHANGED matchIndex
            /\ messages' = messages \ {m}
            /\ UNCHANGED <<currentTerm, state, votedFor, log, commitIndex,
                           lastApplied, electionTimeout, heartbeatTimeout,
                           votesGranted, snapshotLastIndex, snapshotLastTerm,
                           configChangeInProgress, activeNodes>>

LogAppend(s, entry) ==
    /\ state[s] = "LEADER"
    /\ Len(log[s]) < MaxLogLen
    /\ entry.term = currentTerm[s]
    /\ log' = [log EXCEPT ![s] = Append(log[s], entry)]
    /\ UNCHANGED <<currentTerm, state, votedFor, commitIndex, lastApplied,
                   nextIndex, matchIndex, electionTimeout, heartbeatTimeout,
                   messages, votesGranted, snapshotLastIndex, snapshotLastTerm,
                   configChangeInProgress, activeNodes>>

UpdateCommitIndex(s) ==
    /\ state[s] = "LEADER"
    /\ LET indices == {matchIndex[s][t] : t \in activeNodes[s]}
           sortedIndices == CHOOSE seq \in Seq(indices) : 
                           /\ Len(seq) = Cardinality(indices)
                           /\ \A i \in 1..Len(seq)-1 : seq[i] >= seq[i+1]
           majorityIndex == sortedIndices[(Cardinality(activeNodes[s]) + 1) \div 2]
       IN /\ majorityIndex > commitIndex[s]
          /\ GetLogTerm(s, majorityIndex) = currentTerm[s]
          /\ commitIndex' = [commitIndex EXCEPT ![s] = majorityIndex]
    /\ UNCHANGED <<currentTerm, state, votedFor, log, lastApplied, nextIndex,
                   matchIndex, electionTimeout, heartbeatTimeout, messages,
                   votesGranted, snapshotLastIndex, snapshotLastTerm,
                   configChangeInProgress, activeNodes>>

ApplyLog(s) ==
    /\ lastApplied[s] < commitIndex[s]
    /\ lastApplied' = [lastApplied EXCEPT ![s] = lastApplied[s] + 1]
    /\ UNCHANGED <<currentTerm, state, votedFor, log, commitIndex, nextIndex,
                   matchIndex, electionTimeout, heartbeatTimeout, messages,
                   votesGranted, snapshotLastIndex, snapshotLastTerm,
                   configChangeInProgress, activeNodes>>

BeginSnapshot(s) ==
    /\ state[s] \in {"FOLLOWER", "LEADER"}
    /\ lastApplied[s] > snapshotLastIndex[s]
    /\ snapshotLastIndex' = [snapshotLastIndex EXCEPT ![s] = lastApplied[s]]
    /\ snapshotLastTerm' = [snapshotLastTerm EXCEPT ![s] = 
                           GetLogTerm(s, lastApplied[s])]
    /\ log' = [log EXCEPT ![s] = <<>>]
    /\ UNCHANGED <<currentTerm, state, votedFor, commitIndex, lastApplied,
                   nextIndex, matchIndex, electionTimeout, heartbeatTimeout,
                   messages, votesGranted, configChangeInProgress, activeNodes>>

AddNode(s, newNode) ==
    /\ state[s] = "LEADER"
    /\ newNode \notin activeNodes[s]
    /\ ~configChangeInProgress[s]
    /\ LET entry == [term |-> currentTerm[s], 
                     type |-> "CONFIG_ADD", 
                     data |-> newNode]
       IN /\ Len(log[s]) < MaxLogLen
          /\ log' = [log EXCEPT ![s] = Append(log[s], entry)]
          /\ configChangeInProgress' = [configChangeInProgress EXCEPT ![s] = TRUE]
    /\ UNCHANGED <<currentTerm, state, votedFor, commitIndex, lastApplied,
                   nextIndex, matchIndex, electionTimeout, heartbeatTimeout,
                   messages, votesGranted, snapshotLastIndex, snapshotLastTerm,
                   activeNodes>>

RemoveNode(s, oldNode) ==
    /\ state[s] = "LEADER"
    /\ oldNode \in activeNodes[s]
    /\ oldNode # s
    /\ ~configChangeInProgress[s]
    /\ LET entry == [term |-> currentTerm[s], 
                     type |-> "CONFIG_REMOVE", 
                     data |-> oldNode]
       IN /\ Len(log[s]) < MaxLogLen
          /\ log' = [log EXCEPT ![s] = Append(log[s], entry)]
          /\ configChangeInProgress' = [configChangeInProgress EXCEPT ![s] = TRUE]
    /\ UNCHANGED <<currentTerm, state, votedFor, commitIndex, lastApplied,
                   nextIndex, matchIndex, electionTimeout, heartbeatTimeout,
                   messages, votesGranted, snapshotLastIndex, snapshotLastTerm,
                   activeNodes>>

ApplyConfigChange(s) ==
    /\ lastApplied[s] < commitIndex[s]
    /\ LET entryIndex == lastApplied[s] + 1
           entry == log[s][entryIndex - snapshotLastIndex[s]]
       IN /\ entry.type \in {"CONFIG_ADD", "CONFIG_REMOVE"}
          /\ IF entry.type = "CONFIG_ADD"
             THEN activeNodes' = [activeNodes EXCEPT ![s] = 
                                 activeNodes[s] \cup {entry.data}]
             ELSE activeNodes' = [activeNodes EXCEPT ![s] = 
                                 activeNodes[s] \ {entry.data}]
          /\ configChangeInProgress' = [configChangeInProgress EXCEPT ![s] = FALSE]
          /\ lastApplied' = [lastApplied EXCEPT ![s] = entryIndex]
    /\ UNCHANGED <<currentTerm, state, votedFor, log, commitIndex, nextIndex,
                   matchIndex, electionTimeout, heartbeatTimeout, messages,
                   votesGranted, snapshotLastIndex, snapshotLastTerm>>

Next ==
    \/ \E s \in Servers : 
        \/ BecomePreCandidate(s)
        \/ BecomeCandidate(s)
        \/ BecomeLeader(s)
        \/ ElectionTimeout(s)
        \/ HeartbeatTimeout(s)
        \/ UpdateCommitIndex(s)
        \/ ApplyLog(s)
        \/ BeginSnapshot(s)
        \/ ApplyConfigChange(s)
    \/ \E s, t \in Servers :
        \/ SendRequestVote(s, t)
        \/ SendAppendEntries(s, t)
    \/ \E s \in Servers, m \in messages :
        \/ RecvRequestVote(s, m)
        \/ RecvRequestVoteResponse(s, m)
        \/ RecvAppendEntries(s, m)
        \/ RecvAppendEntriesResponse(s, m)
    \/ \E s \in Servers, entry \in LogEntry :
        LogAppend(s, entry)
    \/ \E s \in Servers, n \in Servers :
        \/ AddNode(s, n)
        \/ RemoveNode(s, n)

Spec == Init /\ [][Next]_vars

====