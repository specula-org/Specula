---- MODULE redisraft ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Server, Value, Nil

ASSUME Server \subseteq Nat
ASSUME Nil \notin Server

State == {"Follower", "PreCandidate", "Candidate", "Leader"}
EntryType == {"Normal", "AddNode", "RemoveNode"}

MessageTypes == {"RequestVote", "RequestVoteResponse", "AppendEntries", "AppendEntriesResponse", "InstallSnapshot", "InstallSnapshotResponse"}

(* Helper operators *)
IsQuorum(s, cfg) == Cardinality(s) * 2 > Cardinality(cfg)

LastLogIndex(log) == Len(log)
LastLogTerm(log) == IF Len(log) = 0 THEN 0 ELSE log[Len(log)].term

LogOK(candidateLastLogTerm, candidateLastLogIndex, myLog, mySnapshotIndex, mySnapshotTerm) ==
    LET myLastLogTerm == IF LastLogIndex(myLog) > 0 THEN myLog[LastLogIndex(myLog)].term ELSE mySnapshotTerm
        /\ myLastLogIndex == LastLogIndex(myLog) + mySnapshotIndex
    IN (candidateLastLogTerm > myLastLogTerm) \/
       ((candidateLastLogTerm = myLastLogTerm) /\ (candidateLastLogIndex >= myLastLogIndex))

(* Global variables *)
VARIABLES
    vars,
    messages

LogEntry == [term: Nat, value: Value, type: EntryType, node: Server \cup {Nil}]
Message == [
        type: MessageTypes,
        from: Server,
        to: Server,
        term: Nat,
        m_prevLogIndex: Nat,
        m_prevLogTerm: Nat,
        m_entries: Seq(LogEntry),
        m_leaderCommit: Nat,
        m_lastLogIndex: Nat,
        m_lastLogTerm: Nat,
        m_voteGranted: BOOLEAN,
        m_success: BOOLEAN,
        m_matchIndex: Nat,
        m_prevote: BOOLEAN,
        m_snapshotIndex: Nat,
        m_snapshotTerm: Nat
    ]

TypeOK ==
    /\ vars \in [ Server ->
        [
            state : State,
            currentTerm : Nat,
            votedFor : Server \cup {Nil},
            log : Seq(LogEntry),
            commitIndex : Nat,
            lastApplied : Nat,
            leaderId : Server \cup {Nil},
            votesGranted : SUBSET Server,
            config : SUBSET Server,
            snapshotIndex : Nat,
            snapshotTerm : Nat,
            nextIndex : [Server -> Nat],
            matchIndex : [Server -> Nat]
        ]
    ]
    /\ messages \in Bags(Message)

InitialLog == << >>
InitialConfig == Server

Init ==
    /\ vars = [ i \in Server |->
        [
            state |-> "Follower",
            currentTerm |-> 0,
            votedFor |-> Nil,
            log |-> InitialLog,
            commitIndex |-> 0,
            lastApplied |-> 0,
            leaderId |-> Nil,
            votesGranted |-> {},
            config |-> InitialConfig,
            snapshotIndex |-> 0,
            snapshotTerm |-> 0,
            nextIndex |-> [j \in Server |-> 1],
            matchIndex |-> [j \in Server |-> 0]
        ]
    ]
    /\ messages = EmptyBag

(* Actions *)

BecomeFollower(i, term) ==
    /\ vars[i].currentTerm < term
    /\ vars' = [vars EXCEPT
        ! [i].state = "Follower",
        ! [i].currentTerm = term,
        ! [i].votedFor = Nil,
        ! [i].leaderId = Nil,
        ! [i].votesGranted = {}
    ]
    /\ UNCHANGED messages

ElectionTimeout(i) ==
    /\ vars[i].state \in {"Follower", "PreCandidate"}
    /\ vars[i].leaderId = Nil
    /\ i \in vars[i].config
    /\ vars' = [vars EXCEPT ![i].state = "PreCandidate", ![i].votesGranted = {i}]
    /\ LET
        req(j) == [
            type |-> "RequestVote",
            from |-> i,
            to |-> j,
            term |-> vars[i].currentTerm + 1,
            m_lastLogIndex |-> LastLogIndex(vars[i].log) + vars[i].snapshotIndex,
            m_lastLogTerm |-> IF LastLogIndex(vars[i].log) > 0 THEN vars[i].log[LastLogIndex(vars[i].log)].term ELSE vars[i].snapshotTerm,
            m_prevote |-> TRUE,
            m_prevLogIndex |-> 0, m_prevLogTerm |-> 0, m_entries |-> << >>, m_leaderCommit |-> 0, m_voteGranted |-> FALSE, m_success |-> FALSE, m_matchIndex |-> 0, m_snapshotIndex |-> 0, m_snapshotTerm |-> 0
        ]
       IN messages' = messages \+ Bag({req(j) : j \in vars[i].config \ {i}})

BecomeCandidate(i) ==
    /\ vars[i].state = "PreCandidate"
    /\ IsQuorum(vars[i].votesGranted, vars[i].config)
    /\ vars' = [vars EXCEPT
        ![i].state = "Candidate",
        ![i].currentTerm = vars[i].currentTerm + 1,
        ![i].votedFor = i,
        ![i].votesGranted = {i},
        ![i].leaderId = Nil
    ]
    /\ LET
        req(j) == [
            type |-> "RequestVote",
            from |-> i,
            to |-> j,
            term |-> vars[i].currentTerm + 1,
            m_lastLogIndex |-> LastLogIndex(vars[i].log) + vars[i].snapshotIndex,
            m_lastLogTerm |-> IF LastLogIndex(vars[i].log) > 0 THEN vars[i].log[LastLogIndex(vars[i].log)].term ELSE vars[i].snapshotTerm,
            m_prevote |-> FALSE,
            m_prevLogIndex |-> 0, m_prevLogTerm |-> 0, m_entries |-> << >>, m_leaderCommit |-> 0, m_voteGranted |-> FALSE, m_success |-> FALSE, m_matchIndex |-> 0, m_snapshotIndex |-> 0, m_snapshotTerm |-> 0
        ]
       IN messages' = messages \+ Bag({req(j) : j \in vars[i].config \ {i}})

HandleRequestVote(j, m) ==
    /\ m.type = "RequestVote"
    /\ m.to = j
    /\ LET
        v = vars[j]
        grant ==
            /\ \/ m.prevote
               \/ (m.term > v.currentTerm)
               \/ (m.term = v.currentTerm /\ v.votedFor \in {Nil, m.from})
            /\ LogOK(m.m_lastLogTerm, m.m_lastLogIndex, v.log, v.snapshotIndex, v.snapshotTerm)
        newTerm == IF m.prevote THEN v.currentTerm ELSE m.term
        newVotedFor == IF grant /\ \lnot m.prevote THEN m.from ELSE v.votedFor
        newState == IF (m.term > v.currentTerm) /\ \lnot m.prevote THEN "Follower" ELSE v.state
        resp == [
            type |-> "RequestVoteResponse",
            from |-> j,
            to |-> m.from,
            term |-> newTerm,
            m_voteGranted |-> grant,
            m_prevote |-> m.prevote,
            m_lastLogIndex |-> 0, m_lastLogTerm |-> 0, m_prevLogIndex |-> 0, m_prevLogTerm |-> 0, m_entries |-> << >>, m_leaderCommit |-> 0, m_success |-> FALSE, m_matchIndex |-> 0, m_snapshotIndex |-> 0, m_snapshotTerm |-> 0
        ]
       IN
        /\ messages' = (messages \- Bag({m})) \+ Bag({resp})
        /\ vars' = [vars EXCEPT
            ![j].currentTerm = newTerm,
            ![j].votedFor = newVotedFor,
            ![j].state = newState,
            ![j].leaderId = IF newState = "Follower" THEN Nil ELSE v.leaderId
        ]

HandleRequestVoteResponse(i, m) ==
    /\ m.type = "RequestVoteResponse"
    /\ m.to = i
    /\ LET v = vars[i] IN
    /\ \/ (m.prevote /\ v.state = "PreCandidate" /\ m.term = v.currentTerm + 1)
       \/ (\lnot m.prevote /\ v.state = "Candidate" /\ m.term = v.currentTerm)
    /\ messages' = messages \- Bag({m})
    /\ IF m.m_voteGranted
       THEN vars' = [vars EXCEPT ![i].votesGranted = v.votesGranted \cup {m.from}]
       ELSE UNCHANGED vars

BecomeLeader(i) ==
    /\ vars[i].state = "Candidate"
    /\ IsQuorum(vars[i].votesGranted, vars[i].config)
    /\ LET
        v = vars[i]
        logLen = LastLogIndex(v.log) + v.snapshotIndex
        noopEntry = [term |-> v.currentTerm, value |-> "NoOp", type |-> "Normal", node |-> Nil]
        newLog = Append(v.log, noopEntry)
       IN
        /\ vars' = [vars EXCEPT
            ![i].state = "Leader",
            ![i].leaderId = i,
            ![i].log = newLog,
            ![i].nextIndex = [j \in Server |-> logLen + 2],
            ![i].matchIndex = [j \in Server |-> IF j = i THEN logLen + 1 ELSE 0]
        ]
        /\ UNCHANGED messages

HeartbeatTimeout(i) ==
    /\ vars[i].state = "Leader"
    /\ \E j \in vars[i].config \ {i} : TRUE
    /\ LET
        SendAppendEntries(j) ==
            LET
                v = vars[i]
                prevLogIndex = v.nextIndex[j] - 1
                prevLogTerm = IF prevLogIndex > v.snapshotIndex
                                THEN v.log[prevLogIndex - v.snapshotIndex].term
                                ELSE v.snapshotTerm
                entries = SubSeq(v.log, v.nextIndex[j] - v.snapshotIndex, LastLogIndex(v.log))
            IN [
                type |-> "AppendEntries",
                from |-> i,
                to |-> j,
                term |-> v.currentTerm,
                m_prevLogIndex |-> prevLogIndex,
                m_prevLogTerm |-> prevLogTerm,
                m_entries |-> entries,
                m_leaderCommit |-> v.commitIndex,
                m_lastLogIndex |-> 0, m_lastLogTerm |-> 0, m_voteGranted |-> FALSE, m_success |-> FALSE, m_matchIndex |-> 0, m_prevote |-> FALSE, m_snapshotIndex |-> 0, m_snapshotTerm |-> 0
            ]
       IN
        /\ messages' = messages \+ Bag({SendAppendEntries(j) : j \in vars[i].config \ {i}})
        /\ UNCHANGED vars

HandleAppendEntries(j, m) ==
    /\ m.type = "AppendEntries"
    /\ m.to = j
    /\ LET v = vars[j] IN
    /\ IF m.term < v.currentTerm
       THEN /\ LET resp = [
                    type |-> "AppendEntriesResponse",
                    from |-> j,
                    to |-> m.from,
                    term |-> v.currentTerm,
                    m_success |-> FALSE,
                    m_matchIndex |-> 0,
                    m_prevLogIndex |-> 0, m_prevLogTerm |-> 0, m_entries |-> << >>, m_leaderCommit |-> 0, m_lastLogIndex |-> 0, m_lastLogTerm |-> 0, m_voteGranted |-> FALSE, m_prevote |-> FALSE, m_snapshotIndex |-> 0, m_snapshotTerm |-> 0
                ]
               IN messages' = (messages \- Bag({m})) \+ Bag({resp})
            /\ UNCHANGED vars
       ELSE /\ LET
                logOK ==
                    /\ m.m_prevLogIndex <= LastLogIndex(v.log) + v.snapshotIndex
                    /\ m.m_prevLogIndex >= v.snapshotIndex
                    /\ (m.m_prevLogIndex = v.snapshotIndex => m.m_prevLogTerm = v.snapshotTerm)
                    /\ (m.m_prevLogIndex > v.snapshotIndex => v.log[m.m_prevLogIndex - v.snapshotIndex].term = m.m_prevLogTerm)

                newLog ==
                    IF logOK
                    THEN LET
                            existingEntries = SubSeq(v.log, 1, m.m_prevLogIndex - v.snapshotIndex)
                            newEntries = m.m_entries
                         IN existingEntries \o newEntries
                    ELSE v.log

                newCommitIndex ==
                    IF logOK
                    THEN LET newLastIndex = m.m_prevLogIndex + Len(m.m_entries)
                         IN IF m.m_leaderCommit > v.commitIndex
                            THEN Min({m.m_leaderCommit, newLastIndex})
                            ELSE v.commitIndex
                    ELSE v.commitIndex

                resp == [
                    type |-> "AppendEntriesResponse",
                    from |-> j,
                    to |-> m.from,
                    term |-> m.term,
                    m_success |-> logOK,
                    m_matchIndex |-> IF logOK THEN m.m_prevLogIndex + Len(m.m_entries) ELSE 0,
                    m_prevLogIndex |-> 0, m_prevLogTerm |-> 0, m_entries |-> << >>, m_leaderCommit |-> 0, m_lastLogIndex |-> 0, m_lastLogTerm |-> 0, m_voteGranted |-> FALSE, m_prevote |-> FALSE, m_snapshotIndex |-> 0, m_snapshotTerm |-> 0
                ]
            IN
            /\ messages' = (messages \- Bag({m})) \+ Bag({resp})
            /\ vars' = [vars EXCEPT
                ![j].state = "Follower",
                ![j].currentTerm = m.term,
                ![j].leaderId = m.from,
                ![j].log = newLog,
                ![j].commitIndex = newCommitIndex
            ]

HandleAppendEntriesResponse(i, m) ==
    /\ m.type = "AppendEntriesResponse"
    /\ m.to = i
    /\ vars[i].state = "Leader"
    /\ m.term = vars[i].currentTerm
    /\ messages' = messages \- Bag({m})
    /\ vars' = IF m.m_success
               THEN [vars EXCEPT
                        ![i].nextIndex[m.from] = m.m_matchIndex + 1,
                        ![i].matchIndex[m.from] = m.m_matchIndex
                    ]
               ELSE [vars EXCEPT ![i].nextIndex[m.from] = Max({1, vars[i].nextIndex[m.from] - 1})]

AdvanceCommitIndex(i) ==
    /\ vars[i].state = "Leader"
    /\ LET
        v = vars[i]
        matchSet(idx) == {k \in v.config | v.matchIndex[k] >= idx}
        canCommit(idx) ==
            /\ idx > v.commitIndex
            /\ idx <= LastLogIndex(v.log) + v.snapshotIndex
            /\ idx > v.snapshotIndex
            /\ v.log[idx - v.snapshotIndex].term = v.currentTerm
            /\ IsQuorum(matchSet(idx), v.config)
        newCommitIndex == IF \E idx \in (v.commitIndex+1)..(LastLogIndex(v.log) + v.snapshotIndex) : canCommit(idx)
                          THEN Max({idx \in (v.commitIndex+1)..(LastLogIndex(v.log) + v.snapshotIndex) : canCommit(idx)})
                          ELSE v.commitIndex
       IN
        /\ newCommitIndex > v.commitIndex
        /\ vars' = [vars EXCEPT ![i].commitIndex = newCommitIndex]
        /\ UNCHANGED messages

Apply(i) ==
    /\ vars[i].commitIndex > vars[i].lastApplied
    /\ LET
        v = vars[i]
        newApplied = v.lastApplied + 1
        entry = v.log[newApplied - v.snapshotIndex]
        newConfig =
            CASE entry.type = "AddNode" -> v.config \cup {entry.node}
              [] entry.type = "RemoveNode" -> v.config \ {entry.node}
              [] OTHER -> v.config
       IN
        /\ vars' = [vars EXCEPT
            ![i].lastApplied = newApplied,
            ![i].config = newConfig
        ]
        /\ UNCHANGED messages

ClientRequest(i, val, type, node) ==
    /\ vars[i].state = "Leader"
    /\ LET
        v = vars[i]
        entry = [term |-> v.currentTerm, value |-> val, type |-> type, node |-> node]
        newLog = Append(v.log, entry)
        newMatchIndex = [v.matchIndex EXCEPT ![i] = LastLogIndex(newLog) + v.snapshotIndex]
       IN
        /\ vars' = [vars EXCEPT ![i].log = newLog, ![i].matchIndex = newMatchIndex]
        /\ UNCHANGED messages

TakeSnapshot(i, index) ==
    /\ index > vars[i].snapshotIndex
    /\ index <= vars[i].lastApplied
    /\ LET
        v = vars[i]
        newSnapshotTerm = v.log[index - v.snapshotIndex].term
        newLog = SubSeq(v.log, index - v.snapshotIndex + 1, LastLogIndex(v.log))
       IN
        /\ vars' = [vars EXCEPT
            ![i].snapshotIndex = index,
            ![i].snapshotTerm = newSnapshotTerm,
            ![i].log = newLog
        ]
        /\ UNCHANGED messages

InstallSnapshot(i, j) ==
    /\ vars[i].state = "Leader"
    /\ vars[i].nextIndex[j] <= vars[i].snapshotIndex
    /\ LET
        v = vars[i]
        msg = [
            type |-> "InstallSnapshot",
            from |-> i,
            to |-> j,
            term |-> v.currentTerm,
            m_snapshotIndex |-> v.snapshotIndex,
            m_snapshotTerm |-> v.snapshotTerm,
            m_prevLogIndex |-> 0, m_prevLogTerm |-> 0, m_entries |-> << >>, m_leaderCommit |-> 0, m_lastLogIndex |-> 0, m_lastLogTerm |-> 0, m_voteGranted |-> FALSE, m_success |-> FALSE, m_matchIndex |-> 0, m_prevote |-> FALSE
        ]
       IN
        /\ messages' = messages \+ Bag({msg})
        /\ UNCHANGED vars

HandleInstallSnapshot(j, m) ==
    /\ m.type = "InstallSnapshot"
    /\ m.to = j
    /\ LET v = vars[j] IN
    /\ IF m.term < v.currentTerm
       THEN /\ messages' = messages \- Bag({m})
            /\ UNCHANGED vars
       ELSE /\ LET
                newLog = IF m.m_snapshotIndex > v.snapshotIndex
                         THEN << >>
                         ELSE v.log
                newSnapshotIndex = Max({v.snapshotIndex, m.m_snapshotIndex})
                newSnapshotTerm = IF m.m_snapshotIndex > v.snapshotIndex
                                  THEN m.m_snapshotTerm
                                  ELSE v.snapshotTerm
                newCommitIndex = Max({v.commitIndex, m.m_snapshotIndex})
                newLastApplied = Max({v.lastApplied, m.m_snapshotIndex})
            IN
            /\ vars' = [vars EXCEPT
                ![j].state = "Follower",
                ![j].currentTerm = m.term,
                ![j].leaderId = m.from,
                ![j].log = newLog,
                ![j].snapshotIndex = newSnapshotIndex,
                ![j].snapshotTerm = newSnapshotTerm,
                ![j].commitIndex = newCommitIndex,
                ![j].lastApplied = newLastApplied
            ]
            /\ LET resp = [
                    type |-> "AppendEntriesResponse",
                    from |-> j,
                    to |-> m.from,
                    term |-> m.term,
                    m_success |-> TRUE,
                    m_matchIndex |-> m.m_snapshotIndex,
                    m_prevLogIndex |-> 0, m_prevLogTerm |-> 0, m_entries |-> << >>, m_leaderCommit |-> 0, m_lastLogIndex |-> 0, m_lastLogTerm |-> 0, m_voteGranted |-> FALSE, m_prevote |-> FALSE, m_snapshotIndex |-> 0, m_snapshotTerm |-> 0
                ]
               IN messages' = (messages \- Bag({m})) \+ Bag({resp})

(* Stuttering step for dropped messages *)
DropMessage(m) ==
    /\ messages' = messages \- Bag({m})
    /\ UNCHANGED vars

Next ==
    \/ \E i \in Server:
        \/ ElectionTimeout(i)
        \/ BecomeCandidate(i)
        \/ BecomeLeader(i)
        \/ HeartbeatTimeout(i)
        \/ AdvanceCommitIndex(i)
        \/ Apply(i)
        \/ \E val \in Value, type \in {"Normal"}, node \in {Nil}: ClientRequest(i, val, type, node)
        \/ \E val \in Value, type \in {"AddNode", "RemoveNode"}, node \in Server: ClientRequest(i, val, type, node)
        \/ \E idx \in (vars[i].snapshotIndex + 1)..vars[i].lastApplied: TakeSnapshot(i, idx)
        \/ \E j \in Server: InstallSnapshot(i, j)
    \/ \E m \in DOMAIN messages:
        \/ HandleRequestVote(m.to, m)
        \/ HandleRequestVoteResponse(m.to, m)
        \/ HandleAppendEntries(m.to, m)
        \/ HandleAppendEntriesResponse(m.to, m)
        \/ HandleInstallSnapshot(m.to, m)
        \/ DropMessage(m)
    \/ \E i \in Server, m \in DOMAIN messages:
        \/ (m.type \in {"AppendEntries", "InstallSnapshot", "RequestVoteResponse"} /\ m.to = i /\ m.term > vars[i].currentTerm /\ BecomeFollower(i, m.term))
        \/ (m.type = "RequestVote" /\ \lnot m.m_prevote /\ m.to = i /\ m.term > vars[i].currentTerm /\ BecomeFollower(i, m.term))

Spec == Init /\ [][Next]_<<vars, messages>>

====
