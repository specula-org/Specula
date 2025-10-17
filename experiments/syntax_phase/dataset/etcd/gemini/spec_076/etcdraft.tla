---- MODULE etcdraft ----
EXTENDS Naturals, Sequences, FiniteSets, TLC, Integers

CONSTANTS Servers, Commands, Nil

ASSUME /\ TypeOK(Servers)
       /\ TypeOK(Commands)
       /\ Nil \notin Servers

\* The set of possible server states, from raft.go
ServerStates == {"Follower", "Candidate", "PreCandidate", "Leader"}

\* The set of possible message types, from raftpb.proto
MessageTypes == {
    "MsgHup", "MsgBeat", "MsgProp", "MsgApp", "MsgAppResp", "MsgVote", "MsgVoteResp",
    "MsgSnap", "MsgHeartbeat", "MsgHeartbeatResp", "MsgUnreachable", "MsgSnapStatus",
    "MsgCheckQuorum", "MsgTransferLeader", "MsgTimeoutNow", "MsgReadIndex", "MsgReadIndexResp",
    "MsgPreVote", "MsgPreVoteResp"
}

\* Configuration constants from Config struct
CONSTANT
    HeartbeatInterval,  \* Corresponds to HeartbeatTick
    ElectionTimeoutMin, \* Corresponds to ElectionTick
    ElectionTimeoutMax  \* Corresponds to randomizedElectionTimeout

ASSUME ElectionTimeoutMin > HeartbeatInterval
ASSUME ElectionTimeoutMax >= ElectionTimeoutMin

VARIABLES
    state,          \* Server state: "Follower", "Candidate", "PreCandidate", "Leader"
    currentTerm,    \* Current term for each server
    votedFor,       \* Candidate that received vote in current term
    log,            \* Log entries for each server: << [term: Nat, command: Commands] >>
    commitIndex,    \* Index of highest log entry known to be committed
    appliedIndex,   \* Index of highest log entry applied to state machine
    nextIndex,      \* For leader, index of the next log entry to send to that server
    matchIndex,     \* For leader, index of the highest log entry known to be replicated on server
    votesGranted,   \* For candidates, set of servers that granted a vote
    messages,       \* The set of in-flight messages
    electionTimer,  \* Ticks since last message from leader/election start
    kvStore         \* The key-value store state for each server

vars == <<state, currentTerm, votedFor, log, commitIndex, appliedIndex,
          nextIndex, matchIndex, votesGranted, messages, electionTimer, kvStore>>

QuorumSize == (Cardinality(Servers) \div 2) + 1
IsQuorum(S) == Cardinality(S) >= QuorumSize

LastLogTerm(l) == IF Len(l) = 0 THEN 0 ELSE l[Len(l)].term
LastLogIndex(l) == Len(l)

\* Implements the isUpToDate check from raft.go
IsLogMoreUpToDate(termA, indexA, termB, indexB) ==
    (termA > termB) \/ ((termA = termB) /\ (indexA >= indexB))

TypeOK ==
    /\ state \in [Servers -> ServerStates]
    /\ currentTerm \in [Servers -> Nat]
    /\ votedFor \in [Servers -> Servers \cup {Nil}]
    /\ \A s \in Servers: \A e \in DOMAIN log[s]: log[s][e] \in [term: Nat, command: Commands]
    /\ commitIndex \in [Servers -> Nat]
    /\ appliedIndex \in [Servers -> Nat]
    /\ \A s \in Servers: appliedIndex[s] <= commitIndex[s]
    /\ \A s \in Servers: commitIndex[s] <= Len(log[s])
    /\ nextIndex \in [Servers -> [Servers -> Pos]]
    /\ matchIndex \in [Servers -> [Servers -> Nat]]
    /\ votesGranted \in [Servers -> SUBSET Servers]
    /\ messages \subseteq [type: MessageTypes, from: Servers, to: Servers, term: Nat,
                           logTerm: Nat, index: Nat, entries: Seq, commit: Nat, reject: BOOLEAN]
    /\ electionTimer \in [Servers -> Nat]
    /\ kvStore \in [Servers -> [Commands -> Commands]]

Init ==
    /\ state = [s \in Servers |-> "Follower"]
    /\ currentTerm = [s \in Servers |-> 0]
    /\ votedFor = [s \in Servers |-> Nil]
    /\ log = [s \in Servers |-> << >>]
    /\ commitIndex = [s \in Servers |-> 0]
    /\ appliedIndex = [s \in Servers |-> 0]
    /\ nextIndex = [s \in Servers |-> [t \in Servers |-> 1]]
    /\ matchIndex = [s \in Servers |-> [t \in Servers |-> 0]]
    /\ votesGranted = [s \in Servers |-> {}]
    /\ messages = {}
    /\ electionTimer = [s \in Servers |-> 0]
    /\ kvStore = [s \in Servers |-> [c \in Commands |-> c]]

\* A client submits a command to a server. If it's the leader, it appends it to its log.
ClientRequest(s, cmd) ==
    /\ state[s] = "Leader"
    /\ log' = [log EXCEPT ![s] = Append(log[s], [term |-> currentTerm[s], command |-> cmd])]
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, appliedIndex,
                   nextIndex, matchIndex, votesGranted, messages, electionTimer, kvStore>>

\* A server's election timer increments. This models the passage of time.
Tick(s) ==
    /\ electionTimer' = [electionTimer EXCEPT ![s] = electionTimer[s] + 1]
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, appliedIndex,
                   nextIndex, matchIndex, votesGranted, messages, kvStore>>

\* A follower or candidate times out and starts a pre-election.
FollowerOrCandidateTimesOut(s) ==
    /\ state[s] \in {"Follower", "Candidate"}
    /\ electionTimer[s] >= ElectionTimeoutMin
    /\ state' = [state EXCEPT ![s] = "PreCandidate"]
    /\ votesGranted' = [votesGranted EXCEPT ![s] = {s}]
    /\ electionTimer' = [electionTimer EXCEPT ![s] = 0]
    /\ messages' = messages \cup
        { [ type |-> "MsgPreVote", from |-> s, to |-> t,
            term |-> currentTerm[s] + 1,
            logTerm |-> LastLogTerm(log[s]),
            index |-> LastLogIndex(log[s]),
            entries |-> << >>, commit |-> 0, reject |-> FALSE]
            : t \in Servers \ {s} }
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, appliedIndex,
                   nextIndex, matchIndex, kvStore>>

\* A server receives a PreVote request.
HandlePreVoteRequest(s, msg) ==
    /\ msg \in messages
    /\ msg.type = "MsgPreVote"
    /\ msg.to = s
    /\ LET logOK = IsLogMoreUpToDate(msg.logTerm, msg.index, LastLogTerm(log[s]), LastLogIndex(log[s]))
           termOK = msg.term > currentTerm[s]
           grant = termOK /\ logOK
    IN /\ messages' = (messages \ {msg}) \cup
           {[ type |-> "MsgPreVoteResp", from |-> s, to |-> msg.from,
              term |-> msg.term, reject |-> \neg grant,
              logTerm |-> 0, index |-> 0, entries |-> << >>, commit |-> 0]}
       /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, appliedIndex,
                      nextIndex, matchIndex, votesGranted, electionTimer, kvStore>>

\* A PreCandidate receives a PreVote response.
HandlePreVoteResponse(s, msg) ==
    /\ msg \in messages
    /\ msg.type = "MsgPreVoteResp"
    /\ msg.to = s
    /\ state[s] = "PreCandidate"
    /\ msg.term = currentTerm[s] + 1
    /\ LET newVotes = IF msg.reject THEN votesGranted[s] ELSE votesGranted[s] \cup {msg.from}
    IN /\ IF IsQuorum(newVotes)
          THEN /\ state' = [state EXCEPT ![s] = "Candidate"]
               /\ currentTerm' = [currentTerm EXCEPT ![s] = currentTerm[s] + 1]
               /\ votedFor' = [votedFor EXCEPT ![s] = s]
               /\ votesGranted' = [votesGranted EXCEPT ![s] = {s}]
               /\ electionTimer' = [electionTimer EXCEPT ![s] = 0]
               /\ messages' = (messages \ {msg}) \cup
                   { [ type |-> "MsgVote", from |-> s, to |-> t,
                       term |-> currentTerm[s] + 1,
                       logTerm |-> LastLogTerm(log[s]),
                       index |-> LastLogIndex(log[s]),
                       entries |-> << >>, commit |-> 0, reject |-> FALSE]
                       : t \in Servers \ {s} }
          ELSE /\ votesGranted' = [votesGranted EXCEPT ![s] = newVotes]
               /\ messages' = messages \ {msg}
               /\ UNCHANGED <<state, currentTerm, votedFor, electionTimer>>
       /\ UNCHANGED <<log, commitIndex, appliedIndex, nextIndex, matchIndex, kvStore>>

\* A server receives a RequestVote message.
HandleRequestVote(s, msg) ==
    /\ msg \in messages
    /\ msg.type = "MsgVote"
    /\ msg.to = s
    /\ LET logOK = IsLogMoreUpToDate(msg.logTerm, msg.index, LastLogTerm(log[s]), LastLogIndex(log[s]))
    IN /\ IF msg.term < currentTerm[s]
          THEN (* Stale term, reject vote *)
               /\ messages' = (messages \ {msg}) \cup
                   {[ type |-> "MsgVoteResp", from |-> s, to |-> msg.from,
                      term |-> currentTerm[s], reject |-> TRUE,
                      logTerm |-> 0, index |-> 0, entries |-> << >>, commit |-> 0]}
               /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, appliedIndex,
                              nextIndex, matchIndex, votesGranted, electionTimer, kvStore>>
          ELSE IF msg.term > currentTerm[s]
               THEN (* Higher term, become follower and vote *)
                    /\ LET grant = logOK
                    IN /\ state' = [state EXCEPT ![s] = "Follower"]
                       /\ currentTerm' = [currentTerm EXCEPT ![s] = msg.term]
                       /\ votedFor' = [votedFor EXCEPT ![s] = IF grant THEN msg.from ELSE Nil]
                       /\ electionTimer' = [electionTimer EXCEPT ![s] = 0]
                       /\ votesGranted' = [votesGranted EXCEPT ![s] = {}]
                       /\ messages' = (messages \ {msg}) \cup
                           {[ type |-> "MsgVoteResp", from |-> s, to |-> msg.from,
                              term |-> msg.term, reject |-> \neg grant,
                              logTerm |-> 0, index |-> 0, entries |-> << >>, commit |-> 0]}
                       /\ UNCHANGED <<log, commitIndex, appliedIndex, nextIndex, matchIndex, kvStore>>
               ELSE (* Same term, decide vote *)
                    /\ LET grant = logOK /\ (votedFor[s] \in {Nil, msg.from})
                    IN /\ IF grant
                          THEN votedFor' = [votedFor EXCEPT ![s] = msg.from]
                          ELSE UNCHANGED votedFor
                       /\ messages' = (messages \ {msg}) \cup
                           {[ type |-> "MsgVoteResp", from |-> s, to |-> msg.from,
                              term |-> currentTerm[s], reject |-> \neg grant,
                              logTerm |-> 0, index |-> 0, entries |-> << >>, commit |-> 0]}
                       /\ UNCHANGED <<state, currentTerm, log, commitIndex, appliedIndex,
                                      nextIndex, matchIndex, votesGranted, electionTimer, kvStore>>

\* A candidate receives a vote response.
HandleRequestVoteResponse(s, msg) ==
    /\ msg \in messages
    /\ msg.type = "MsgVoteResp"
    /\ msg.to = s
    /\ state[s] = "Candidate"
    /\ msg.term = currentTerm[s]
    /\ LET newVotes = IF msg.reject THEN votesGranted[s] ELSE votesGranted[s] \cup {msg.from}
    IN /\ IF IsQuorum(newVotes)
          THEN /\ state' = [state EXCEPT ![s] = "Leader"]
               /\ nextIndex' = [nextIndex EXCEPT ![s] = [t \in Servers |-> LastLogIndex(log[s]) + 1]]
               /\ matchIndex' = [matchIndex EXCEPT ![s] = [t \in Servers |-> 0]]
               /\ messages' = (messages \ {msg}) \cup
                   { [ type |-> "MsgApp", from |-> s, to |-> t,
                       term |-> currentTerm[s],
                       logTerm |-> LastLogTerm(log[s]),
                       index |-> LastLogIndex(log[s]),
                       entries |-> << >>,
                       commit |-> commitIndex[s],
                       reject |-> FALSE]
                       : t \in Servers \ {s} }
               /\ UNCHANGED <<votesGranted>>
          ELSE /\ votesGranted' = [votesGranted EXCEPT ![s] = newVotes]
               /\ messages' = messages \ {msg}
               /\ UNCHANGED <<state, nextIndex, matchIndex>>
       /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, appliedIndex, electionTimer, kvStore>>

\* A leader sends AppendEntries (can be heartbeat or with data).
LeaderSendsAppendEntries(s) ==
    /\ state[s] = "Leader"
    /\ \E t \in Servers \ {s}:
        /\ LET prevIndex = nextIndex[s][t] - 1
               prevTerm = IF prevIndex > 0 THEN log[s][prevIndex].term ELSE 0
               newEntries = SubSeq(log[s], nextIndex[s][t], Len(log[s]))
        IN messages' = messages \cup
            {[ type |-> "MsgApp", from |-> s, to |-> t,
               term |-> currentTerm[s],
               logTerm |-> prevTerm,
               index |-> prevIndex,
               entries |-> newEntries,
               commit |-> commitIndex[s],
               reject |-> FALSE]}
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, appliedIndex,
                   nextIndex, matchIndex, votesGranted, electionTimer, kvStore>>

\* A server receives an AppendEntries message.
HandleAppendEntries(s, msg) ==
    /\ msg \in messages
    /\ msg.type = "MsgApp"
    /\ msg.to = s
    /\ IF msg.term < currentTerm[s]
       THEN /\ messages' = (messages \ {msg}) \cup
                {[ type |-> "MsgAppResp", from |-> s, to |-> msg.from,
                   term |-> currentTerm[s], reject |-> TRUE,
                   logTerm |-> 0, index |-> 0, entries |-> << >>, commit |-> 0]}
            /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, appliedIndex,
                           nextIndex, matchIndex, votesGranted, electionTimer, kvStore>>
       ELSE /\ LET newTerm = msg.term
                 newVotedFor = IF msg.term > currentTerm[s] THEN Nil ELSE votedFor[s]
                 logOK = (msg.index = 0) \/
                           (msg.index <= Len(log[s]) /\ log[s][msg.index].term = msg.logTerm)
            IN /\ state' = [state EXCEPT ![s] = "Follower"]
               /\ currentTerm' = [currentTerm EXCEPT ![s] = newTerm]
               /\ votedFor' = [votedFor EXCEPT ![s] = newVotedFor]
               /\ electionTimer' = [electionTimer EXCEPT ![s] = 0]
               /\ votesGranted' = [votesGranted EXCEPT ![s] = {}]
               /\ IF logOK
                  THEN /\ LET newLog = SubSeq(log[s], 1, msg.index) \o msg.entries
                       IN /\ log' = [log EXCEPT ![s] = newLog]
                          /\ IF msg.commit > commitIndex[s]
                             THEN commitIndex' = [commitIndex EXCEPT ![s] = Min({msg.commit, Len(newLog)})]
                             ELSE UNCHANGED commitIndex
                          /\ messages' = (messages \ {msg}) \cup
                              {[ type |-> "MsgAppResp", from |-> s, to |-> msg.from,
                                 term |-> newTerm, reject |-> FALSE,
                                 logTerm |-> 0, index |-> LastLogIndex(newLog),
                                 entries |-> << >>, commit |-> 0]}
                  ELSE /\ UNCHANGED <<log, commitIndex>>
                       /\ messages' = (messages \ {msg}) \cup
                           {[ type |-> "MsgAppResp", from |-> s, to |-> msg.from,
                              term |-> newTerm, reject |-> TRUE,
                              logTerm |-> 0, index |-> 0,
                              entries |-> << >>, commit |-> 0]}
               /\ UNCHANGED <<appliedIndex, nextIndex, matchIndex, kvStore>>

\* A leader receives an AppendEntries response.
HandleAppendEntriesResponse(s, msg) ==
    /\ msg \in messages
    /\ msg.type = "MsgAppResp"
    /\ msg.to = s
    /\ state[s] = "Leader"
    /\ msg.term = currentTerm[s]
    /\ IF msg.reject
       THEN /\ nextIndex' = [nextIndex EXCEPT ![s] = [nextIndex[s] EXCEPT ![msg.from] = nextIndex[s][msg.from] - 1]]
            /\ UNCHANGED matchIndex
       ELSE /\ nextIndex' = [nextIndex EXCEPT ![s] = [nextIndex[s] EXCEPT ![msg.from] = msg.index + 1]]
            /\ matchIndex' = [matchIndex EXCEPT ![s] = [matchIndex[s] EXCEPT ![msg.from] = msg.index]]
    /\ messages' = messages \ {msg}
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, appliedIndex,
                   votesGranted, electionTimer, kvStore>>

\* A leader advances its commit index.
LeaderAdvancesCommitIndex(s) ==
    /\ state[s] = "Leader"
    /\ LET newCommitIndex =
        Max({i \in 1..Len(log[s]) |
            /\ i > commitIndex[s]
            /\ log[s][i].term = currentTerm[s]
            /\ IsQuorum({t \in Servers | matchIndex[s][t] >= i} \cup {s})
        } \cup {commitIndex[s]})
    /\ commitIndex' = [commitIndex EXCEPT ![s] = newCommitIndex]
    /\ UNCHANGED <<state, currentTerm, votedFor, log, appliedIndex,
                   nextIndex, matchIndex, votesGranted, messages, electionTimer, kvStore>>

\* A server applies committed entries to its state machine.
ApplyToStateMachine(s) ==
    /\ commitIndex[s] > appliedIndex[s]
    /\ LET i = appliedIndex[s] + 1
           entry = log[s][i]
    /\ appliedIndex' = [appliedIndex EXCEPT ![s] = i]
    /\ kvStore' = [kvStore EXCEPT ![s] = [kvStore[s] EXCEPT ![entry.command] = entry.command]]
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex,
                   nextIndex, matchIndex, votesGranted, messages, electionTimer>>

Next ==
    \/ \E s \in Servers, cmd \in Commands: ClientRequest(s, cmd)
    \/ \E s \in Servers:
        \/ Tick(s)
        \/ FollowerOrCandidateTimesOut(s)
        \/ LeaderAdvancesCommitIndex(s)
        \/ ApplyToStateMachine(s)
        \/ LeaderSendsAppendEntries(s)
    \/ \E s \in Servers, msg \in messages:
        \/ HandlePreVoteRequest(s, msg)
        \/ HandlePreVoteResponse(s, msg)
        \/ HandleRequestVote(s, msg)
        \/ HandleRequestVoteResponse(s, msg)
        \/ HandleAppendEntries(s, msg)
        \/ HandleAppendEntriesResponse(s, msg)

Spec == Init /\ [][Next]_vars

\* --- Invariants ---

\* There is at most one leader in any given term.
AtMostOneLeaderPerTerm ==
    \A t \in Nat:
        Cardinality({s \in Servers | state[s] = "Leader" /\ currentTerm[s] = t}) <= 1

\* If an entry is committed, it must be present in the logs of all future leaders.
LeaderLogsComplete ==
    \A s1, s2 \in Servers:
        IF state[s1] = "Leader" /\ state[s2] = "Leader" /\ currentTerm[s1] < currentTerm[s2]
        THEN \A i \in 1..commitIndex[s1]: log[s1][i] \in {log[s2][j] : j \in DOMAIN log[s2]}

\* If two logs contain an entry with the same index and term, the logs are identical up to that index.
LogMatching ==
    \A s1, s2 \in Servers:
        \A i \in DOMAIN log[s1] \cap DOMAIN log[s2]:
            IF log[s1][i].term = log[s2][i].term
            THEN log[s1][i] = log[s2][i]

\* Committed entries are present in the logs of all servers up to their commitIndex.
CommittedEntriesAreDurable ==
    \A s1, s2 \in Servers:
        \A i \in 1..Min({commitIndex[s1], commitIndex[s2]}):
            IF log[s1][i].term = log[s2][i].term
            THEN log[s1][i] = log[s2][i]

\* If a server has applied an entry at a given index, no other server will ever apply a different entry at the same index.
StateMachineSafety ==
    \A s1, s2 \in Servers:
        \A i \in 1..Min({appliedIndex[s1], appliedIndex[s2]}):
            log[s1][i] = log[s2][i]

====
