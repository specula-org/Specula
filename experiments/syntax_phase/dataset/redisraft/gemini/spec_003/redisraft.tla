---- MODULE redisraft ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags, Integers

CONSTANTS
    Server,
    Value,
    Nil

ASSUME Server = {"s1", "s2", "s3"}
ASSUME Value = {"v1", "v2"}

VARIABLES
    state,
    currentTerm,
    votedFor,
    log,
    commitIndex,
    lastApplied,
    nextIndex,
    matchIndex,
    votesGranted,
    messages,
    server_config,
    lastIncludedIndex,
    lastIncludedTerm,
    config_change_in_flight

vars == <<state, currentTerm, votedFor, log, commitIndex, lastApplied,
          nextIndex, matchIndex, votesGranted, messages, server_config,
          lastIncludedIndex, lastIncludedTerm, config_change_in_flight>>

TypeOK ==
    /\ state \in [Server -> {"Follower", "PreCandidate", "Candidate", "Leader"}]
    /\ currentTerm \in [Server -> Nat]
    /\ votedFor \in [Server -> Server \cup {Nil}]
    /\ \A s \in Server: \A e \in DOMAIN log[s]:
        log[s][e] \in [term: Nat, command: Value \cup SUBSET Server, type: {"NORMAL", "CONFIG"}]
    /\ commitIndex \in [Server -> Nat]
    /\ lastApplied \in [Server -> Nat]
    /\ nextIndex \in [Server -> [Server -> Nat]]
    /\ matchIndex \in [Server -> [Server -> Nat]]
    /\ votesGranted \in [Server -> SUBSET Server]
    /\ IsBag(messages)
    /\ server_config \in [Server -> SUBSET Server]
    /\ lastIncludedIndex \in [Server -> Nat]
    /\ lastIncludedTerm \in [Server -> Nat]
    /\ config_change_in_flight \in [Server -> BOOLEAN]

LogEntry(s, idx) ==
    IF idx > lastIncludedIndex[s]
    THEN log[s][idx - lastIncludedIndex[s]]
    ELSE [term |-> lastIncludedTerm[s], command |-> Nil, type |-> "NORMAL"]

LogTerm(s, idx) ==
    IF idx = 0 THEN 0
    ELSE IF idx = lastIncludedIndex[s]
    THEN lastIncludedTerm[s]
    ELSE LogEntry(s, idx).term

LastLogIndex(s) == Len(log[s]) + lastIncludedIndex[s]
LastLogTerm(s) == LogTerm(s, LastLogIndex(s))
Quorum(cfg) == (Cardinality(cfg) \div 2) + 1

Init ==
    /\ state = [s \in Server |-> "Follower"]
    /\ currentTerm = [s \in Server |-> 0]
    /\ votedFor = [s \in Server |-> Nil]
    /\ log = [s \in Server |-> <<>>]
    /\ commitIndex = [s \in Server |-> 0]
    /\ lastApplied = [s \in Server |-> 0]
    /\ nextIndex = [s \in Server |-> [t \in Server |-> 1]]
    /\ matchIndex = [s \in Server |-> [t \in Server |-> 0]]
    /\ votesGranted = [s \in Server |-> {}]
    /\ messages = EmptyBag
    /\ server_config = [s \in Server |-> Server]
    /\ lastIncludedIndex = [s \in Server |-> 0]
    /\ lastIncludedTerm = [s \in Server |-> 0]
    /\ config_change_in_flight = [s \in Server |-> FALSE]

\* State Transitions
BecomeFollower(s, term) ==
    /\ state' = [state EXCEPT ![s] = "Follower"]
    /\ currentTerm' = [currentTerm EXCEPT ![s] = term]
    /\ votedFor' = [votedFor EXCEPT ![s] = Nil]
    /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex,
                   votesGranted, messages, server_config, lastIncludedIndex,
                   lastIncludedTerm, config_change_in_flight>>

BecomePreCandidate(s) ==
    /\ state' = [state EXCEPT ![s] = "PreCandidate"]
    /\ votesGranted' = [votesGranted EXCEPT ![s] = {}]
    /\ messages' = messages (+) Bag({[
            type |-> "RequestVote",
            from |-> s,
            to |-> t,
            term |-> currentTerm[s] + 1,
            lastLogIndex |-> LastLogIndex(s),
            lastLogTerm |-> LastLogTerm(s),
            prevote |-> TRUE
        ] : t \in server_config[s] \ {s}})
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, lastApplied,
                   nextIndex, matchIndex, server_config, lastIncludedIndex,
                   lastIncludedTerm, config_change_in_flight>>

BecomeCandidate(s) ==
    /\ state' = [state EXCEPT ![s] = "Candidate"]
    /\ currentTerm' = [currentTerm EXCEPT ![s] = currentTerm[s] + 1]
    /\ votedFor' = [votedFor EXCEPT ![s] = s]
    /\ votesGranted' = [votesGranted EXCEPT ![s] = {s}]
    /\ messages' = messages (+) Bag({[
            type |-> "RequestVote",
            from |-> s,
            to |-> t,
            term |-> currentTerm[s] + 1,
            lastLogIndex |-> LastLogIndex(s),
            lastLogTerm |-> LastLogTerm(s),
            prevote |-> FALSE
        ] : t \in server_config[s] \ {s}})
    /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex,
                   server_config, lastIncludedIndex, lastIncludedTerm,
                   config_change_in_flight>>

BecomeLeader(s) ==
    /\ state' = [state EXCEPT ![s] = "Leader"]
    /\ nextIndex' = [nextIndex EXCEPT ![s] = [t \in Server |-> LastLogIndex(s) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![s] = [t \in Server |-> 0]]
    /\ log' = [log EXCEPT ![s] = Append(log[s], [term |-> currentTerm[s], command |-> Nil, type |-> "NORMAL"])]
    /\ UNCHANGED <<currentTerm, votedFor, commitIndex, lastApplied,
                   votesGranted, messages, server_config, lastIncludedIndex,
                   lastIncludedTerm, config_change_in_flight>>

\* Vote Processing
HandleRequestVote(s, m) ==
    LET lastLogOk == \/ m.lastLogTerm > LastLogTerm(s)
                     \/ /\ m.lastLogTerm = LastLogTerm(s)
                        /\ m.lastLogIndex >= LastLogIndex(s)
        grant == \/ m.term > currentTerm[s]
                 \/ /\ m.term = currentTerm[s]
                    /\ votedFor[s] \in {Nil, m.from}
    IN
    /\ m.type = "RequestVote"
    /\ m.to = s
    /\ LET resp == [
            type |-> "RequestVoteResponse",
            from |-> s,
            to |-> m.from,
            term |-> IF m.term < currentTerm[s] THEN currentTerm[s] ELSE m.term,
            voteGranted |-> grant /\ lastLogOk,
            prevote |-> m.prevote
        ]
    IN
    /\ messages' = (messages (-) Bag({m})) (+) Bag({resp})
    /\ IF resp.voteGranted /\ NOT m.prevote
       THEN /\ votedFor' = [votedFor EXCEPT ![s] = m.from]
            /\ IF m.term > currentTerm[s]
               THEN /\ state' = [state EXCEPT ![s] = "Follower"]
                    /\ currentTerm' = [currentTerm EXCEPT ![s] = m.term]
               ELSE UNCHANGED <<state, currentTerm>>
       ELSE /\ UNCHANGED <<votedFor, state, currentTerm>>
    /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex,
                   votesGranted, server_config, lastIncludedIndex,
                   lastIncludedTerm, config_change_in_flight>>

HandleRequestVoteResponse(s, m) ==
    /\ m.type = "RequestVoteResponse"
    /\ m.to = s
    /\ \/ /\ m.term > currentTerm[s]
          /\ messages' = messages (-) Bag({m})
          /\ state' = [state EXCEPT ![s] = "Follower"]
          /\ currentTerm' = [currentTerm EXCEPT ![s] = m.term]
          /\ votedFor' = [votedFor EXCEPT ![s] = Nil]
          /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex,
                         votesGranted, server_config, lastIncludedIndex,
                         lastIncludedTerm, config_change_in_flight>>
       \/ /\ m.term <= currentTerm[s]
          /\ \/ /\ m.voteGranted = FALSE
                /\ messages' = messages (-) Bag({m})
                /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied,
                               nextIndex, matchIndex, votesGranted, server_config,
                               lastIncludedIndex, lastIncludedTerm, config_change_in_flight>>
             \/ /\ m.voteGranted = TRUE
                /\ LET newVotes == votesGranted[s] \cup {m.from}
                IN
                /\ \/ /\ ( \/ (state[s] = "PreCandidate" /\ m.prevote = FALSE)
                           \/ (state[s] = "Candidate" /\ m.prevote = TRUE)
                           \/ Cardinality(newVotes) < Quorum(server_config[s]) )
                      /\ messages' = messages (-) Bag({m})
                      /\ votesGranted' = [votesGranted EXCEPT ![s] = newVotes]
                      /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex,
                                     lastApplied, nextIndex, matchIndex, server_config,
                                     lastIncludedIndex, lastIncludedTerm,
                                     config_change_in_flight>>
                   \/ /\ state[s] = "PreCandidate" /\ m.prevote
                      /\ Cardinality(newVotes) >= Quorum(server_config[s])
                      /\ state' = [state EXCEPT ![s] = "Candidate"]
                      /\ currentTerm' = [currentTerm EXCEPT ![s] = currentTerm[s] + 1]
                      /\ votedFor' = [votedFor EXCEPT ![s] = s]
                      /\ votesGranted' = [votesGranted EXCEPT ![s] = {s}]
                      /\ messages' = (messages (-) Bag({m})) (+) Bag({[
                              type |-> "RequestVote", from |-> s, to |-> t,
                              term |-> currentTerm[s] + 1, lastLogIndex |-> LastLogIndex(s),
                              lastLogTerm |-> LastLogTerm(s), prevote |-> FALSE
                          ] : t \in server_config[s] \ {s}})
                      /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex,
                                     server_config, lastIncludedIndex, lastIncludedTerm,
                                     config_change_in_flight>>
                   \/ /\ state[s] = "Candidate" /\ NOT m.prevote
                      /\ Cardinality(newVotes) >= Quorum(server_config[s])
                      /\ state' = [state EXCEPT ![s] = "Leader"]
                      /\ nextIndex' = [nextIndex EXCEPT ![s] = [t \in Server |-> LastLogIndex(s) + 1]]
                      /\ matchIndex' = [matchIndex EXCEPT ![s] = [t \in Server |-> 0]]
                      /\ log' = [log EXCEPT ![s] = Append(log[s], [term |-> currentTerm[s], command |-> Nil, type |-> "NORMAL"])]
                      /\ messages' = messages (-) Bag({m})
                      /\ votesGranted' = [votesGranted EXCEPT ![s] = newVotes]
                      /\ UNCHANGED <<currentTerm, votedFor, commitIndex, lastApplied,
                                     server_config, lastIncludedIndex,
                                     lastIncludedTerm, config_change_in_flight>>

\* Log Replication
SendAppendEntries(s, t) ==
    /\ state[s] = "Leader"
    /\ t \in server_config[s] \ {s}
    /\ LET prevLogIndex == nextIndex[s][t] - 1
    IN
    \/ /\ prevLogIndex < lastIncludedIndex[s]
       /\ LET msg == [
               type |-> "InstallSnapshot",
               from |-> s,
               to |-> t,
               term |-> currentTerm[s],
               lastIncludedIndex |-> lastIncludedIndex[s],
               lastIncludedTerm |-> lastIncludedTerm[s]
           ]
       IN
       /\ messages' = messages (+) Bag({msg})
       /\ UNCHANGED nextIndex
    \/ /\ prevLogIndex >= lastIncludedIndex[s]
       /\ LET prevLogTerm == LogTerm(s, prevLogIndex)
              entriesToSend == SubSeq(log[s], prevLogIndex - lastIncludedIndex[s] + 1, Len(log[s]))
              msg == [
                  type |-> "AppendEntries",
                  from |-> s,
                  to |-> t,
                  term |-> currentTerm[s],
                  prevLogIndex |-> prevLogIndex,
                  prevLogTerm |-> prevLogTerm,
                  entries |-> entriesToSend,
                  leaderCommit |-> commitIndex[s]
              ]
          IN
          /\ messages' = messages (+) Bag({msg})
          /\ nextIndex' = [nextIndex EXCEPT ![s] = [nextIndex[s] EXCEPT ![t] = LastLogIndex(s) + 1]]
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied,
                   matchIndex, votesGranted, server_config, lastIncludedIndex,
                   lastIncludedTerm, config_change_in_flight>>

HandleAppendEntries(s, m) ==
    /\ m.type = "AppendEntries"
    /\ m.to = s
    /\ LET resp ==
        IF m.term < currentTerm[s]
        THEN [ type |-> "AppendEntriesResponse", from |-> s, to |-> m.from,
               term |-> currentTerm[s], success |-> FALSE, matchIndex |-> 0 ]
        ELSE LET logOk == \/ m.prevLogIndex = 0
                         \/ /\ m.prevLogIndex <= LastLogIndex(s)
                            /\ LogTerm(s, m.prevLogIndex) = m.prevLogTerm
             IN [ type |-> "AppendEntriesResponse", from |-> s, to |-> m.from,
                  term |-> m.term, success |-> logOk,
                  matchIndex |-> IF logOk THEN m.prevLogIndex + Len(m.entries) ELSE LastLogIndex(s) ]
    IN
    /\ messages' = (messages (-) Bag({m})) (+) Bag({resp})
    /\ IF m.term < currentTerm[s]
       THEN UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied,
                       nextIndex, matchIndex, votesGranted, server_config,
                       lastIncludedIndex, lastIncludedTerm, config_change_in_flight>>
       ELSE /\ state' = [state EXCEPT ![s] = "Follower"]
            /\ currentTerm' = [currentTerm EXCEPT ![s] = m.term]
            /\ votedFor' = [votedFor EXCEPT ![s] = Nil]
            /\ IF resp.success
               THEN /\ LET conflictingIndices == { i \in 1..Len(m.entries) :
                                                   /\ m.prevLogIndex + i <= LastLogIndex(s)
                                                   /\ LogTerm(s, m.prevLogIndex + i) # m.entries[i].term }
                       IN
                       LET newLog ==
                           IF conflictingIndices = {}
                           THEN LET existingEntries == SubSeq(log[s], 1, m.prevLogIndex - lastIncludedIndex[s])
                                IN existingEntries \o m.entries
                           ELSE LET conflictIndex == Min(conflictingIndices)
                                    existingEntries == SubSeq(log[s], 1, m.prevLogIndex + conflictIndex - 1 - lastIncludedIndex[s])
                                    newEntries == SubSeq(m.entries, conflictIndex, Len(m.entries))
                                IN existingEntries \o newEntries
                       IN
                       LET newLastLogIndex == Len(newLog) + lastIncludedIndex[s]
                       IN
                       /\ log' = [log EXCEPT ![s] = newLog]
                       /\ commitIndex' = [commitIndex EXCEPT ![s] = Max({commitIndex[s], Min({m.leaderCommit, newLastLogIndex})})]
               ELSE /\ log' = log
                    /\ commitIndex' = commitIndex
            /\ UNCHANGED <<lastApplied, nextIndex, matchIndex, votesGranted,
                           server_config, lastIncludedIndex, lastIncludedTerm,
                           config_change_in_flight>>

HandleAppendEntriesResponse(s, m) ==
    /\ m.type = "AppendEntriesResponse"
    /\ m.to = s
    /\ state[s] = "Leader"
    /\ messages' = messages (-) Bag({m})
    /\ \/ /\ m.term > currentTerm[s]
          /\ state' = [state EXCEPT ![s] = "Follower"]
          /\ currentTerm' = [currentTerm EXCEPT ![s] = m.term]
          /\ votedFor' = [votedFor EXCEPT ![s] = Nil]
          /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex,
                         votesGranted, server_config, lastIncludedIndex,
                         lastIncludedTerm, config_change_in_flight>>
       \/ /\ m.term <= currentTerm[s]
          /\ IF m.success
             THEN /\ LET newMatchIndex_s = [matchIndex[s] EXCEPT ![m.from] = m.matchIndex]
                  IN
                  /\ matchIndex' = [matchIndex EXCEPT ![s] = newMatchIndex_s]
                  /\ nextIndex' = [nextIndex EXCEPT ![s] = [nextIndex[s] EXCEPT ![m.from] = m.matchIndex + 1]]
                  /\ LET potentialCommits == {i \in (commitIndex[s] + 1)..LastLogIndex(s) :
                                                   /\ LogTerm(s, i) = currentTerm[s]
                                                   /\ Cardinality({t \in server_config[s] : newMatchIndex_s[t] >= i}) >= Quorum(server_config[s])}
                  IN commitIndex' = [commitIndex EXCEPT ![s] = IF potentialCommits = {} THEN commitIndex[s] ELSE Max(potentialCommits)]
             ELSE /\ nextIndex' = [nextIndex EXCEPT ![s] = [nextIndex[s] EXCEPT ![m.from] = Max({1, nextIndex[s][m.from] - 1})]]
                  /\ UNCHANGED <<matchIndex, commitIndex>>
          /\ UNCHANGED <<state, currentTerm, votedFor, log, lastApplied, votesGranted, server_config,
                         lastIncludedIndex, lastIncludedTerm, config_change_in_flight>>

\* Leader Operations
Heartbeat(s) ==
    /\ state[s] = "Leader"
    /\ messages' = messages (+) Bag({[
            type |-> "AppendEntries",
            from |-> s,
            to |-> t,
            term |-> currentTerm[s],
            prevLogIndex |-> LastLogIndex(s),
            prevLogTerm |-> LastLogTerm(s),
            entries |-> <<>>,
            leaderCommit |-> commitIndex[s]
        ] : t \in server_config[s] \ {s}})
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied,
                   nextIndex, matchIndex, votesGranted, server_config,
                   lastIncludedIndex, lastIncludedTerm, config_change_in_flight>>

\* Election Management
ElectionTimeout(s) ==
    /\ state[s] \in {"Follower", "PreCandidate", "Candidate"}
    /\ BecomePreCandidate(s)

\* Log Management
ClientRequest(s, cmd, type) ==
    /\ state[s] = "Leader"
    /\ IF type = "CONFIG"
       THEN NOT config_change_in_flight[s]
       ELSE TRUE
    /\ log' = [log EXCEPT ![s] = Append(log[s], [term |-> currentTerm[s], command |-> cmd, type |-> type])]
    /\ config_change_in_flight' =
        IF type = "CONFIG"
        THEN [config_change_in_flight EXCEPT ![s] = TRUE]
        ELSE config_change_in_flight
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, lastApplied,
                   nextIndex, matchIndex, votesGranted, messages, server_config,
                   lastIncludedIndex, lastIncludedTerm>>

Apply(s) ==
    /\ commitIndex[s] > lastApplied[s]
    /\ LET applyIdx == lastApplied[s] + 1
           entryToApply == LogEntry(s, applyIdx)
    IN
    /\ lastApplied' = [lastApplied EXCEPT ![s] = applyIdx]
    /\ IF entryToApply.type = "CONFIG"
       THEN /\ server_config' = [server_config EXCEPT ![s] = entryToApply.command]
            /\ config_change_in_flight' = [config_change_in_flight EXCEPT ![s] = FALSE]
       ELSE UNCHANGED <<server_config, config_change_in_flight>>
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex,
                   nextIndex, matchIndex, votesGranted, messages,
                   lastIncludedIndex, lastIncludedTerm>>

\* Snapshot Handling
BeginSnapshot(s) ==
    /\ commitIndex[s] > lastIncludedIndex[s]
    /\ LET snapshotIndex == commitIndex[s]
           snapshotTerm == LogTerm(s, snapshotIndex)
           newLog == SubSeq(log[s], snapshotIndex - lastIncludedIndex[s] + 1, Len(log[s]))
    IN
    /\ lastIncludedIndex' = [lastIncludedIndex EXCEPT ![s] = snapshotIndex]
    /\ lastIncludedTerm' = [lastIncludedTerm EXCEPT ![s] = snapshotTerm]
    /\ log' = [log EXCEPT ![s] = newLog]
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, lastApplied,
                   nextIndex, matchIndex, votesGranted, messages, server_config,
                   config_change_in_flight>>

HandleSnapshot(s, m) ==
    /\ m.type = "InstallSnapshot"
    /\ m.to = s
    /\ messages' = messages (-) Bag({m})
    /\ IF m.term < currentTerm[s]
       THEN UNCHANGED vars
       ELSE /\ state' = [state EXCEPT ![s] = "Follower"]
            /\ currentTerm' = [currentTerm EXCEPT ![s] = m.term]
            /\ votedFor' = [votedFor EXCEPT ![s] = Nil]
            /\ IF m.lastIncludedIndex > lastIncludedIndex[s]
               THEN /\ LET newLog ==
                           IF /\ LastLogIndex(s) > m.lastIncludedIndex
                              /\ LogTerm(s, m.lastIncludedIndex) = m.lastIncludedTerm
                           THEN SubSeq(log[s], m.lastIncludedIndex - lastIncludedIndex[s] + 1, Len(log[s]))
                           ELSE <<>>
                    IN log' = [log EXCEPT ![s] = newLog]
                    /\ lastIncludedIndex' = [lastIncludedIndex EXCEPT ![s] = m.lastIncludedIndex]
                    /\ lastIncludedTerm' = [lastIncludedTerm EXCEPT ![s] = m.lastIncludedTerm]
                    /\ commitIndex' = [commitIndex EXCEPT ![s] = Max({commitIndex[s], m.lastIncludedIndex})]
                    /\ lastApplied' = [lastApplied EXCEPT ![s] = Max({lastApplied[s], m.lastIncludedIndex})]
               ELSE UNCHANGED <<log, lastIncludedIndex, lastIncludedTerm, commitIndex, lastApplied>>
            /\ UNCHANGED <<nextIndex, matchIndex, votesGranted, server_config, config_change_in_flight>>

Next ==
    \/ \E s \in Server: ElectionTimeout(s)
    \/ \E s \in Server:
        \/ \E m \in BagToSet(messages): HandleRequestVote(s, m)
        \/ \E m \in BagToSet(messages): HandleRequestVoteResponse(s, m)
        \/ \E m \in BagToSet(messages): HandleAppendEntries(s, m)
        \/ \E m \in BagToSet(messages): HandleAppendEntriesResponse(s, m)
        \/ \E m \in BagToSet(messages): HandleSnapshot(s, m)
        \/ \E t \in Server: SendAppendEntries(s, t)
        \/ Heartbeat(s)
        \/ \E cmd \in Value: ClientRequest(s, cmd, "NORMAL")
        \/ \E cfg \in SUBSET Server: ClientRequest(s, cfg, "CONFIG")
        \/ Apply(s)
        \/ BeginSnapshot(s)

Spec == Init /\ [][Next]_vars

=============================================================================
