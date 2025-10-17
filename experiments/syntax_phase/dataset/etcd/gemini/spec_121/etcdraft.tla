---- MODULE etcdraft ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS
    \* @type: Set(Str);
    Servers,
    \* @type: Set(Str);
    Commands

ASSUME
    /\ Servers = {"n1", "n2", "n3"}
    /\ Commands = {"v1", "v2"}

Quorum == (Cardinality(Servers) \div 2) + 1

\* Message Types
MessageTypes ==
    { "ClientRequest", "PreVoteRequest", "PreVoteResponse",
      "VoteRequest", "VoteResponse", "AppendEntriesRequest", "AppendEntriesResponse" }

\* Node States
NodeStates == {"Follower", "PreCandidate", "Candidate", "Leader"}

\* Log entry is a record of term and command
LogEntry(t, c) == [term |-> t, command |-> c]

\* An empty log entry used for initial leader commit
EmptyLogEntry(t) == [term |-> t, command |-> ""]

\* A sentinel value for no one voted for
Nil == "Nil"

VARIABLES
    \* @type: [key: Str, val: Str];
    state,
    \* @type: [key: Str, val: Int];
    currentTerm,
    \* @type: [key: Str, val: Str];
    votedFor,
    \* @type: [key: Str, val: Seq([term: Int, command: Str])];
    log,
    \* @type: [key: Str, val: Int];
    commitIndex,
    \* @type: Bag([type: Str, from: Str, to: Str, term: Int, m_index: Int, m_log_term: Int, entries: Seq([term: Int, command: Str]), commit: Int, vote_granted: Bool, command: Str]);
    messages,
    \* @type: [key: Str, val: Str];
    leader,
    \* @type: [key: Str, val: Set(Str)];
    votesGranted,
    \* @type: [key: Str, val: Int];
    preVoteTerm,
    \* @type: [key: Str, val: Set(Str)];
    preVotesGranted

vars == <<state, currentTerm, votedFor, log, commitIndex, messages, leader, votesGranted, preVoteTerm, preVotesGranted>>

\* Helper operators for log management
LastLogIndex(l) == Len(l)
LastLogTerm(l) == IF Len(l) = 0 THEN 0 ELSE l[Len(l)].term

\* Candidate's log is at least as up-to-date as receiver's log
IsUpToDate(candidateLastLogTerm, candidateLastLogIndex, receiverLog) ==
    LET receiverLastLogTerm == LastLogTerm(receiverLog)
        receiverLastLogIndex == LastLogIndex(receiverLog)
    IN
    \/ candidateLastLogTerm > receiverLastLogTerm
    \/ /\ candidateLastLogTerm = receiverLastLogTerm
       /\ candidateLastLogIndex >= receiverLastLogIndex

\* ==================================================================================================================
\* Initial state of the system
\* ==================================================================================================================
Init ==
    /\ state = [s \in Servers |-> "Follower"]
    /\ currentTerm = [s \in Servers |-> 0]
    /\ votedFor = [s \in Servers |-> Nil]
    /\ log = [s \in Servers |-> <<>>]
    /\ commitIndex = [s \in Servers |-> 0]
    /\ leader = [s \in Servers |-> Nil]
    /\ votesGranted = [s \in Servers |-> {}]
    /\ preVoteTerm = [s \in Servers |-> 0]
    /\ preVotesGranted = [s \in Servers |-> {}]
    /\ messages = EmptyBag

\* ==================================================================================================================
\* State Transitions (Actions)
\* ==================================================================================================================

\* A server becomes a follower if it discovers a higher term
BecomeFollower(s, term) ==
    /\ state' = [state EXCEPT ![s] = "Follower"]
    /\ currentTerm' = [currentTerm EXCEPT ![s] = term]
    /\ votedFor' = [votedFor EXCEPT ![s] = Nil]
    /\ leader' = [leader EXCEPT ![s] = Nil]
    /\ votesGranted' = [votesGranted EXCEPT ![s] = {}]
    /\ preVotesGranted' = [preVotesGranted EXCEPT ![s] = {}]

\* A follower/candidate times out and starts a pre-vote campaign
Timeout(s) ==
    /\ state[s] \in {"Follower", "Candidate"}
    /\ state' = [state EXCEPT ![s] = "PreCandidate"]
    /\ preVoteTerm' = [preVoteTerm EXCEPT ![s] = currentTerm[s] + 1]
    /\ preVotesGranted' = [preVotesGranted EXCEPT ![s] = {s}]
    /\ messages' = messages \cup
        { [ type |-> "PreVoteRequest",
            from |-> s,
            to |-> peer,
            term |-> currentTerm[s] + 1,
            m_log_term |-> LastLogTerm(log[s]),
            m_index |-> LastLogIndex(log[s])
          ] : peer \in Servers \ {s} }
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, leader, votesGranted>>

\* A server handles a PreVoteRequest
HandlePreVoteRequest(s) ==
    \E m \in messages:
        /\ m.type = "PreVoteRequest"
        /\ m.to = s
        /\ LET candidateId == m.from
               candidateTerm == m.term
               candidateLastLogTerm == m.m_log_term
               candidateLastLogIndex == m.m_index
           IN
           /\ \/ /\ candidateTerm < currentTerm[s]
                 /\ messages' = messages (-) {m} \cup
                      { [ type |-> "PreVoteResponse",
                          from |-> s,
                          to |-> candidateId,
                          term |-> currentTerm[s],
                          vote_granted |-> FALSE
                        ] }
                 /\ UNCHANGED <<vars \ {messages}>>
              \/ /\ candidateTerm >= currentTerm[s]
                 /\ IsUpToDate(candidateLastLogTerm, candidateLastLogIndex, log[s])
                 /\ messages' = messages (-) {m} \cup
                      { [ type |-> "PreVoteResponse",
                          from |-> s,
                          to |-> candidateId,
                          term |-> candidateTerm,
                          vote_granted |-> TRUE
                        ] }
                 /\ UNCHANGED <<vars \ {messages}>>
              \/ /\ candidateTerm >= currentTerm[s]
                 /\ \lnot IsUpToDate(candidateLastLogTerm, candidateLastLogIndex, log[s])
                 /\ messages' = messages (-) {m} \cup
                      { [ type |-> "PreVoteResponse",
                          from |-> s,
                          to |-> candidateId,
                          term |-> candidateTerm,
                          vote_granted |-> FALSE
                        ] }
                 /\ UNCHANGED <<vars \ {messages}>>

\* A PreCandidate handles a PreVoteResponse
HandlePreVoteResponse(s) ==
    \E m \in messages:
        /\ m.type = "PreVoteResponse"
        /\ m.to = s
        /\ state[s] = "PreCandidate"
        /\ m.term = preVoteTerm[s]
        /\ LET voter == m.from
           IN
           /\ \/ /\ m.vote_granted
                 /\ LET newPreVotes == preVotesGranted[s] \cup {voter}
                    IN
                    /\ \/ Cardinality(newPreVotes) < Quorum
                          /\ preVotesGranted' = [preVotesGranted EXCEPT ![s] = newPreVotes]
                          /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leader, votesGranted, preVoteTerm>>
                       \/ /\ Cardinality(newPreVotes) >= Quorum
                          /\ state' = [state EXCEPT ![s] = "Candidate"]
                          /\ currentTerm' = [currentTerm EXCEPT ![s] = currentTerm[s] + 1]
                          /\ votedFor' = [votedFor EXCEPT ![s] = s]
                          /\ votesGranted' = [votesGranted EXCEPT ![s] = {s}]
                          /\ leader' = [leader EXCEPT ![s] = Nil]
                          /\ messages' = messages (-) {m} \cup
                                { [ type |-> "VoteRequest",
                                    from |-> s,
                                    to |-> peer,
                                    term |-> currentTerm[s] + 1,
                                    m_log_term |-> LastLogTerm(log[s]),
                                    m_index |-> LastLogIndex(log[s])
                                  ] : peer \in Servers \ {s} }
                          /\ UNCHANGED <<log, commitIndex, preVoteTerm, preVotesGranted>>
              \/ /\ \lnot m.vote_granted
                 /\ UNCHANGED <<vars \ {messages}>>
           /\ messages' = messages (-) {m}

\* A server handles a VoteRequest
HandleVoteRequest(s) ==
    \E m \in messages:
        /\ m.type = "VoteRequest"
        /\ m.to = s
        /\ LET candidateId == m.from
               candidateTerm == m.term
               candidateLastLogTerm == m.m_log_term
               candidateLastLogIndex == m.m_index
           IN
           /\ \/ /\ candidateTerm < currentTerm[s]
                 /\ messages' = messages (-) {m} \cup
                      { [ type |-> "VoteResponse",
                          from |-> s,
                          to |-> candidateId,
                          term |-> currentTerm[s],
                          vote_granted |-> FALSE
                        ] }
                 /\ UNCHANGED <<vars \ {messages}>>
              \/ /\ candidateTerm > currentTerm[s]
                 /\ IsUpToDate(candidateLastLogTerm, candidateLastLogIndex, log[s])
                 /\ state' = [state EXCEPT ![s] = "Follower"]
                 /\ currentTerm' = [currentTerm EXCEPT ![s] = candidateTerm]
                 /\ votedFor' = [votedFor EXCEPT ![s] = candidateId]
                 /\ leader' = [leader EXCEPT ![s] = Nil]
                 /\ messages' = messages (-) {m} \cup
                      { [ type |-> "VoteResponse",
                          from |-> s,
                          to |-> candidateId,
                          term |-> candidateTerm,
                          vote_granted |-> TRUE
                        ] }
                 /\ UNCHANGED <<log, commitIndex, votesGranted, preVoteTerm, preVotesGranted>>
              \/ /\ candidateTerm = currentTerm[s]
                 /\ (votedFor[s] = Nil \/ votedFor[s] = candidateId)
                 /\ IsUpToDate(candidateLastLogTerm, candidateLastLogIndex, log[s])
                 /\ votedFor' = [votedFor EXCEPT ![s] = candidateId]
                 /\ messages' = messages (-) {m} \cup
                      { [ type |-> "VoteResponse",
                          from |-> s,
                          to |-> candidateId,
                          term |-> candidateTerm,
                          vote_granted |-> TRUE
                        ] }
                 /\ UNCHANGED <<state, currentTerm, log, commitIndex, leader, votesGranted, preVoteTerm, preVotesGranted>>
              \/ /\ \lnot ( \/ candidateTerm < currentTerm[s]
                           \/ (candidateTerm > currentTerm[s] /\ IsUpToDate(candidateLastLogTerm, candidateLastLogIndex, log[s]))
                           \/ (candidateTerm = currentTerm[s] /\ (votedFor[s] = Nil \/ votedFor[s] = candidateId) /\ IsUpToDate(candidateLastLogTerm, candidateLastLogIndex, log[s]))
                         )
                 /\ messages' = messages (-) {m} \cup
                      { [ type |-> "VoteResponse",
                          from |-> s,
                          to |-> candidateId,
                          term |-> currentTerm[s],
                          vote_granted |-> FALSE
                        ] }
                 /\ UNCHANGED <<vars \ {messages}>>

\* A Candidate handles a VoteResponse
HandleVoteResponse(s) ==
    \E m \in messages:
        /\ m.type = "VoteResponse"
        /\ m.to = s
        /\ state[s] = "Candidate"
        /\ m.term = currentTerm[s]
        /\ LET voter == m.from
           IN
           /\ \/ /\ m.vote_granted
                 /\ LET newVotes == votesGranted[s] \cup {voter}
                    IN
                    /\ \/ Cardinality(newVotes) < Quorum
                          /\ votesGranted' = [votesGranted EXCEPT ![s] = newVotes]
                          /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leader, preVoteTerm, preVotesGranted>>
                       \/ /\ Cardinality(newVotes) >= Quorum
                          /\ state' = [state EXCEPT ![s] = "Leader"]
                          /\ leader' = [leader EXCEPT ![s] = s]
                          /\ log' = [log EXCEPT ![s] = log[s] \o <<EmptyLogEntry(currentTerm[s])>>]
                          /\ messages' = messages (-) {m} \cup
                                { [ type |-> "AppendEntriesRequest",
                                    from |-> s,
                                    to |-> peer,
                                    term |-> currentTerm[s],
                                    m_index |-> LastLogIndex(log[s]),
                                    m_log_term |-> LastLogTerm(log[s]),
                                    entries |-> <<EmptyLogEntry(currentTerm[s])>>,
                                    commit |-> commitIndex[s]
                                  ] : peer \in Servers \ {s} }
                          /\ UNCHANGED <<currentTerm, votedFor, commitIndex, votesGranted, preVoteTerm, preVotesGranted>>
              \/ /\ \lnot m.vote_granted
                 /\ UNCHANGED <<vars \ {messages}>>
           /\ messages' = messages (-) {m}

\* A client sends a request to the leader
ClientRequest(s) ==
    /\ state[s] = "Leader"
    /\ \E cmd \in Commands:
        /\ LET newEntry == LogEntry(currentTerm[s], cmd)
               newLog == log[s] \o <<newEntry>>
           IN
           /\ log' = [log EXCEPT ![s] = newLog]
           /\ UNCHANGED <<vars \ {log}>>

\* A leader sends AppendEntries (including heartbeats)
LeaderSendAppendEntries(s) ==
    /\ state[s] = "Leader"
    /\ \E peer \in Servers \ {s}:
        /\ LET prevLogIndex == LastLogIndex(log[s])
               prevLogTerm == LastLogTerm(log[s])
           IN
           /\ messages' = messages \cup
                { [ type |-> "AppendEntriesRequest",
                    from |-> s,
                    to |-> peer,
                    term |-> currentTerm[s],
                    m_index |-> prevLogIndex,
                    m_log_term |-> prevLogTerm,
                    entries |-> <<>>,
                    commit |-> commitIndex[s]
                  ] }
           /\ UNCHANGED <<vars \ {messages}>>

\* A server handles an AppendEntriesRequest
HandleAppendEntriesRequest(s) ==
    \E m \in messages:
        /\ m.type = "AppendEntriesRequest"
        /\ m.to = s
        /\ LET leaderId == m.from
               leaderTerm == m.term
               prevLogIndex == m.m_index
               prevLogTerm == m.m_log_term
               entries == m.entries
               leaderCommit == m.commit
           IN
           /\ \/ /\ leaderTerm < currentTerm[s]
                 /\ messages' = messages (-) {m} \cup
                      { [ type |-> "AppendEntriesResponse",
                          from |-> s,
                          to |-> leaderId,
                          term |-> currentTerm[s],
                          success |-> FALSE,
                          m_index |-> 0
                        ] }
                 /\ UNCHANGED <<vars \ {messages}>>
              \/ /\ leaderTerm >= currentTerm[s]
                 /\ \/ leaderTerm > currentTerm[s]
                    \/ state[s] = "Candidate"
                 /\ state' = [state EXCEPT ![s] = "Follower"]
                 /\ currentTerm' = [currentTerm EXCEPT ![s] = leaderTerm]
                 /\ votedFor' = [votedFor EXCEPT ![s] = Nil]
                 /\ leader' = [leader EXCEPT ![s] = leaderId]
                 /\ \/ /\ \/ prevLogIndex > LastLogIndex(log[s])
                          \/ /\ prevLogIndex > 0
                             /\ log[s][prevLogIndex].term /= prevLogTerm
                       /\ messages' = messages (-) {m} \cup
                            { [ type |-> "AppendEntriesResponse",
                                from |-> s,
                                to |-> leaderId,
                                term |-> currentTerm[s],
                                success |-> FALSE,
                                m_index |-> LastLogIndex(log[s])
                              ] }
                       /\ UNCHANGED <<log, commitIndex, votesGranted, preVoteTerm, preVotesGranted>>
                    \/ /\ \/ prevLogIndex = 0
                          \/ /\ prevLogIndex > 0
                             /\ log[s][prevLogIndex].term = prevLogTerm
                       /\ LET newLog == SubSeq(log[s], 1, prevLogIndex) \o entries
                          IN
                          /\ log' = [log EXCEPT ![s] = newLog]
                          /\ commitIndex' = [commitIndex EXCEPT ![s] = min({leaderCommit, LastLogIndex(newLog)})]
                          /\ messages' = messages (-) {m} \cup
                               { [ type |-> "AppendEntriesResponse",
                                   from |-> s,
                                   to |-> leaderId,
                                   term |-> currentTerm[s],
                                   success |-> TRUE,
                                   m_index |-> LastLogIndex(newLog)
                                 ] }
                          /\ UNCHANGED <<votesGranted, preVoteTerm, preVotesGranted>>

\* A leader handles an AppendEntriesResponse
HandleAppendEntriesResponse(s) ==
    \E m \in messages:
        /\ m.type = "AppendEntriesResponse"
        /\ m.to = s
        /\ state[s] = "Leader"
        /\ m.term = currentTerm[s]
        /\ LET followerId == m.from
           IN
           /\ \/ /\ m.success
                 /\ LET newCommitIndex ==
                        CHOOSE N \in commitIndex[s]+1..LastLogIndex(log[s]):
                            /\ log[s][N].term = currentTerm[s]
                            /\ Cardinality({p \in Servers |-> m.m_index >= N} \cup {s}) >= Quorum
                    IN
                    /\ commitIndex' = [commitIndex EXCEPT ![s] = newCommitIndex]
                    /\ UNCHANGED <<state, currentTerm, votedFor, log, leader, votesGranted, preVoteTerm, preVotesGranted>>
              \/ /\ \lnot m.success
                 /\ UNCHANGED <<vars \ {messages}>>
           /\ messages' = messages (-) {m}

\* A message from a future term forces a server to become a follower
StaleTerm(s) ==
    \E m \in messages:
        /\ m.to = s
        /\ m.term > currentTerm[s]
        /\ \/ m.type \in {"VoteRequest", "AppendEntriesRequest"}
           /\ BecomeFollower(s, m.term)
           /\ messages' = messages
           /\ UNCHANGED <<log, commitIndex, votesGranted, preVoteTerm, preVotesGranted>>
        \/ /\ m.type \in {"PreVoteResponse", "VoteResponse", "AppendEntriesResponse"}
           /\ state[s] \in {"Candidate", "Leader"}
           /\ BecomeFollower(s, m.term)
           /\ messages' = messages (-) {m}
           /\ UNCHANGED <<log, commitIndex, votesGranted, preVoteTerm, preVotesGranted>>

\* A message can be dropped
DropMessage ==
    \E m \in messages:
        /\ messages' = messages (-) {m}
        /\ UNCHANGED <<vars \ {messages}>>

\* ==================================================================================================================
\* The Next-State Relation
\* ==================================================================================================================
Next ==
    \/ \E s \in Servers:
        \/ Timeout(s)
        \/ HandlePreVoteRequest(s)
        \/ HandlePreVoteResponse(s)
        \/ HandleVoteRequest(s)
        \/ HandleVoteResponse(s)
        \/ ClientRequest(s)
        \/ LeaderSendAppendEntries(s)
        \/ HandleAppendEntriesRequest(s)
        \/ HandleAppendEntriesResponse(s)
        \/ StaleTerm(s)
    \/ DropMessage

Spec == Init /\ [][Next]_vars

====