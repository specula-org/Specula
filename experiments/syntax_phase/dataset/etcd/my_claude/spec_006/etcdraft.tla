---- MODULE etcdraft ----

EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Servers, MaxTerm, MaxLogLen

VARIABLES
    currentTerm,
    votedFor,
    log,
    state,
    commitIndex,
    nextIndex,
    matchIndex,
    votes,
    messages,
    electionTimeout,
    heartbeatTimeout

vars == <<currentTerm, votedFor, log, state, commitIndex, nextIndex, matchIndex, votes, messages, electionTimeout, heartbeatTimeout>>

States == {"Follower", "PreCandidate", "Candidate", "Leader"}

MessageTypes == {"MsgHup", "MsgVote", "MsgVoteResp", "MsgPreVote", "MsgPreVoteResp", "MsgApp", "MsgAppResp", "MsgHeartbeat", "MsgHeartbeatResp", "MsgProp"}

Message == [type: MessageTypes, term: Nat, from: Servers, to: Servers, logTerm: Nat, index: Nat, entries: Seq(Nat), commit: Nat, reject: BOOLEAN]

Init ==
    /\ currentTerm = [s \in Servers |-> 1]
    /\ votedFor = [s \in Servers |-> "None"]
    /\ log = [s \in Servers |-> <<>>]
    /\ state = [s \in Servers |-> "Follower"]
    /\ commitIndex = [s \in Servers |-> 0]
    /\ nextIndex = [s \in Servers |-> [t \in Servers |-> 1]]
    /\ matchIndex = [s \in Servers |-> [t \in Servers |-> 0]]
    /\ votes = [s \in Servers |-> {}]
    /\ messages = {}
    /\ electionTimeout = [s \in Servers |-> FALSE]
    /\ heartbeatTimeout = [s \in Servers |-> FALSE]

Send(m) == messages' = messages \cup {m}

Reply(m, response) == 
    messages' = (messages \ {m}) \cup {response}

Discard(m) == messages' = messages \ {m}

LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)]

IsUpToDate(candidateLastTerm, candidateLastIndex, voterLastTerm, voterLastIndex) ==
    \/ candidateLastTerm > voterLastTerm
    \/ /\ candidateLastTerm = voterLastTerm
       /\ candidateLastIndex >= voterLastIndex

BecomeFollower(s, term) ==
    /\ currentTerm' = [currentTerm EXCEPT ![s] = term]
    /\ state' = [state EXCEPT ![s] = "Follower"]
    /\ votedFor' = [votedFor EXCEPT ![s] = "None"]
    /\ votes' = [votes EXCEPT ![s] = {}]
    /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex>>

BecomePreCandidate(s) ==
    /\ state' = [state EXCEPT ![s] = "PreCandidate"]
    /\ votes' = [votes EXCEPT ![s] = {}]
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex>>

BecomeCandidate(s) ==
    /\ currentTerm' = [currentTerm EXCEPT ![s] = currentTerm[s] + 1]
    /\ state' = [state EXCEPT ![s] = "Candidate"]
    /\ votedFor' = [votedFor EXCEPT ![s] = s]
    /\ votes' = [votes EXCEPT ![s] = {s}]
    /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex>>

BecomeLeader(s) ==
    /\ state' = [state EXCEPT ![s] = "Leader"]
    /\ nextIndex' = [nextIndex EXCEPT ![s] = [t \in Servers |-> Len(log[s]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![s] = [t \in Servers |-> 0]]
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, votes>>

ElectionTimeout(s) ==
    /\ electionTimeout[s] = TRUE
    /\ state[s] \in {"Follower", "PreCandidate", "Candidate"}
    /\ electionTimeout' = [electionTimeout EXCEPT ![s] = FALSE]
    /\ IF state[s] = "Follower"
       THEN /\ BecomePreCandidate(s)
            /\ Send([type |-> "MsgPreVote", term |-> currentTerm[s] + 1, from |-> s, to |-> t, 
                     logTerm |-> LastTerm(log[s]), index |-> Len(log[s]), 
                     entries |-> <<>>, commit |-> 0, reject |-> FALSE]) \in {TRUE : t \in Servers \ {s}}
       ELSE IF state[s] = "PreCandidate"
            THEN /\ BecomeCandidate(s)
                 /\ Send([type |-> "MsgVote", term |-> currentTerm'[s], from |-> s, to |-> t,
                          logTerm |-> LastTerm(log[s]), index |-> Len(log[s]),
                          entries |-> <<>>, commit |-> 0, reject |-> FALSE]) \in {TRUE : t \in Servers \ {s}}
            ELSE /\ BecomeCandidate(s)
                 /\ Send([type |-> "MsgVote", term |-> currentTerm'[s], from |-> s, to |-> t,
                          logTerm |-> LastTerm(log[s]), index |-> Len(log[s]),
                          entries |-> <<>>, commit |-> 0, reject |-> FALSE]) \in {TRUE : t \in Servers \ {s}}
    /\ UNCHANGED <<heartbeatTimeout>>

HeartbeatTimeout(s) ==
    /\ heartbeatTimeout[s] = TRUE
    /\ state[s] = "Leader"
    /\ heartbeatTimeout' = [heartbeatTimeout EXCEPT ![s] = FALSE]
    /\ \A t \in Servers \ {s} :
        Send([type |-> "MsgHeartbeat", term |-> currentTerm[s], from |-> s, to |-> t,
              logTerm |-> 0, index |-> 0, entries |-> <<>>, commit |-> commitIndex[s], reject |-> FALSE])
    /\ UNCHANGED <<currentTerm, votedFor, log, state, commitIndex, nextIndex, matchIndex, votes, electionTimeout>>

HandleVoteRequest(m) ==
    LET s == m.to
        candidateLastTerm == m.logTerm
        candidateLastIndex == m.index
        voterLastTerm == LastTerm(log[s])
        voterLastIndex == Len(log[s])
        canVote == /\ \/ votedFor[s] = "None"
                      \/ votedFor[s] = m.from
                   /\ m.term >= currentTerm[s]
                   /\ IsUpToDate(candidateLastTerm, candidateLastIndex, voterLastTerm, voterLastIndex)
    IN
    /\ m.type = "MsgVote"
    /\ IF m.term > currentTerm[s]
       THEN /\ BecomeFollower(s, m.term)
            /\ IF canVote
               THEN /\ votedFor' = [votedFor' EXCEPT ![s] = m.from]
                    /\ Reply(m, [type |-> "MsgVoteResp", term |-> m.term, from |-> s, to |-> m.from,
                                 logTerm |-> 0, index |-> 0, entries |-> <<>>, commit |-> 0, reject |-> FALSE])
               ELSE Reply(m, [type |-> "MsgVoteResp", term |-> m.term, from |-> s, to |-> m.from,
                              logTerm |-> 0, index |-> 0, entries |-> <<>>, commit |-> 0, reject |-> TRUE])
       ELSE IF m.term = currentTerm[s] /\ canVote
            THEN /\ votedFor' = [votedFor EXCEPT ![s] = m.from]
                 /\ Reply(m, [type |-> "MsgVoteResp", term |-> m.term, from |-> s, to |-> m.from,
                              logTerm |-> 0, index |-> 0, entries |-> <<>>, commit |-> 0, reject |-> FALSE])
                 /\ UNCHANGED <<currentTerm, state, log, commitIndex, nextIndex, matchIndex, votes>>
            ELSE /\ Reply(m, [type |-> "MsgVoteResp", term |-> m.term, from |-> s, to |-> m.from,
                              logTerm |-> 0, index |-> 0, entries |-> <<>>, commit |-> 0, reject |-> TRUE])
                 /\ UNCHANGED <<currentTerm, votedFor, state, log, commitIndex, nextIndex, matchIndex, votes>>
    /\ UNCHANGED <<electionTimeout, heartbeatTimeout>>

HandlePreVoteRequest(m) ==
    LET s == m.to
        candidateLastTerm == m.logTerm
        candidateLastIndex == m.index
        voterLastTerm == LastTerm(log[s])
        voterLastIndex == Len(log[s])
        canVote == IsUpToDate(candidateLastTerm, candidateLastIndex, voterLastTerm, voterLastIndex)
    IN
    /\ m.type = "MsgPreVote"
    /\ IF canVote
       THEN Reply(m, [type |-> "MsgPreVoteResp", term |-> m.term, from |-> s, to |-> m.from,
                      logTerm |-> 0, index |-> 0, entries |-> <<>>, commit |-> 0, reject |-> FALSE])
       ELSE Reply(m, [type |-> "MsgPreVoteResp", term |-> m.term, from |-> s, to |-> m.from,
                      logTerm |-> 0, index |-> 0, entries |-> <<>>, commit |-> 0, reject |-> TRUE])
    /\ UNCHANGED <<currentTerm, votedFor, log, state, commitIndex, nextIndex, matchIndex, votes, electionTimeout, heartbeatTimeout>>

HandleVoteResponse(m) ==
    LET s == m.to
        newVotes == IF m.reject THEN votes[s] ELSE votes[s] \cup {m.from}
        majority == Cardinality(newVotes) * 2 > Cardinality(Servers)
    IN
    /\ m.type = "MsgVoteResp"
    /\ state[s] = "Candidate"
    /\ m.term = currentTerm[s]
    /\ votes' = [votes EXCEPT ![s] = newVotes]
    /\ IF majority /\ ~m.reject
       THEN BecomeLeader(s)
       ELSE UNCHANGED <<currentTerm, votedFor, log, state, commitIndex, nextIndex, matchIndex>>
    /\ Discard(m)
    /\ UNCHANGED <<electionTimeout, heartbeatTimeout>>

HandlePreVoteResponse(m) ==
    LET s == m.to
        newVotes == IF m.reject THEN votes[s] ELSE votes[s] \cup {m.from}
        majority == Cardinality(newVotes) * 2 > Cardinality(Servers)
    IN
    /\ m.type = "MsgPreVoteResp"
    /\ state[s] = "PreCandidate"
    /\ votes' = [votes EXCEPT ![s] = newVotes]
    /\ IF majority /\ ~m.reject
       THEN /\ BecomeCandidate(s)
            /\ \A t \in Servers \ {s} :
                Send([type |-> "MsgVote", term |-> currentTerm'[s], from |-> s, to |-> t,
                      logTerm |-> LastTerm(log[s]), index |-> Len(log[s]),
                      entries |-> <<>>, commit |-> 0, reject |-> FALSE])
       ELSE UNCHANGED <<currentTerm, votedFor, log, state, commitIndex, nextIndex, matchIndex>>
    /\ Discard(m)
    /\ UNCHANGED <<electionTimeout, heartbeatTimeout>>

HandleAppendEntries(m) ==
    LET s == m.to
        prevLogIndex == m.index
        prevLogTerm == m.logTerm
        logOk == \/ prevLogIndex = 0
                 \/ /\ prevLogIndex <= Len(log[s])
                    /\ prevLogIndex > 0 => log[s][prevLogIndex] = prevLogTerm
    IN
    /\ m.type = "MsgApp"
    /\ IF m.term > currentTerm[s]
       THEN BecomeFollower(s, m.term)
       ELSE UNCHANGED <<currentTerm, votedFor, state, votes>>
    /\ IF logOk
       THEN /\ log' = [log EXCEPT ![s] = SubSeq(log[s], 1, prevLogIndex) \o m.entries]
            /\ commitIndex' = [commitIndex EXCEPT ![s] = Min(m.commit, Len(log'[s]))]
            /\ Reply(m, [type |-> "MsgAppResp", term |-> currentTerm'[s], from |-> s, to |-> m.from,
                         logTerm |-> 0, index |-> Len(log'[s]), entries |-> <<>>, commit |-> 0, reject |-> FALSE])
       ELSE /\ Reply(m, [type |-> "MsgAppResp", term |-> currentTerm'[s], from |-> s, to |-> m.from,
                         logTerm |-> 0, index |-> 0, entries |-> <<>>, commit |-> 0, reject |-> TRUE])
            /\ UNCHANGED <<log, commitIndex>>
    /\ UNCHANGED <<nextIndex, matchIndex, electionTimeout, heartbeatTimeout>>

HandleAppendResponse(m) ==
    LET s == m.to
    IN
    /\ m.type = "MsgAppResp"
    /\ state[s] = "Leader"
    /\ m.term = currentTerm[s]
    /\ IF ~m.reject
       THEN /\ nextIndex' = [nextIndex EXCEPT ![s][m.from] = m.index + 1]
            /\ matchIndex' = [matchIndex EXCEPT ![s][m.from] = m.index]
       ELSE /\ nextIndex' = [nextIndex EXCEPT ![s][m.from] = Max(1, nextIndex[s][m.from] - 1)]
            /\ UNCHANGED matchIndex
    /\ Discard(m)
    /\ UNCHANGED <<currentTerm, votedFor, log, state, commitIndex, votes, electionTimeout, heartbeatTimeout>>

HandleHeartbeat(m) ==
    LET s == m.to
    IN
    /\ m.type = "MsgHeartbeat"
    /\ IF m.term > currentTerm[s]
       THEN BecomeFollower(s, m.term)
       ELSE UNCHANGED <<currentTerm, votedFor, state, votes>>
    /\ commitIndex' = [commitIndex EXCEPT ![s] = Min(m.commit, Len(log[s]))]
    /\ Reply(m, [type |-> "MsgHeartbeatResp", term |-> currentTerm'[s], from |-> s, to |-> m.from,
                 logTerm |-> 0, index |-> 0, entries |-> <<>>, commit |-> 0, reject |-> FALSE])
    /\ UNCHANGED <<log, nextIndex, matchIndex, electionTimeout, heartbeatTimeout>>

HandleHeartbeatResponse(m) ==
    /\ m.type = "MsgHeartbeatResp"
    /\ Discard(m)
    /\ UNCHANGED <<currentTerm, votedFor, log, state, commitIndex, nextIndex, matchIndex, votes, electionTimeout, heartbeatTimeout>>

ClientProposal(s, entry) ==
    /\ state[s] = "Leader"
    /\ Len(log[s]) < MaxLogLen
    /\ log' = [log EXCEPT ![s] = Append(log[s], entry)]
    /\ UNCHANGED <<currentTerm, votedFor, state, commitIndex, nextIndex, matchIndex, votes, messages, electionTimeout, heartbeatTimeout>>

AppendEntries(s, t) ==
    /\ state[s] = "Leader"
    /\ nextIndex[s][t] <= Len(log[s])
    /\ LET prevLogIndex == nextIndex[s][t] - 1
           prevLogTerm == IF prevLogIndex = 0 THEN 0 ELSE log[s][prevLogIndex]
           entries == SubSeq(log[s], nextIndex[s][t], Len(log[s]))
       IN Send([type |-> "MsgApp", term |-> currentTerm[s], from |-> s, to |-> t,
                logTerm |-> prevLogTerm, index |-> prevLogIndex, entries |-> entries,
                commit |-> commitIndex[s], reject |-> FALSE])
    /\ UNCHANGED <<currentTerm, votedFor, log, state, commitIndex, nextIndex, matchIndex, votes, electionTimeout, heartbeatTimeout>>

AdvanceCommitIndex(s) ==
    /\ state[s] = "Leader"
    /\ LET newCommitIndex == CHOOSE i \in (commitIndex[s] + 1)..Len(log[s]) :
                                /\ log[s][i] = currentTerm[s]
                                /\ Cardinality({t \in Servers : matchIndex[s][t] >= i}) * 2 > Cardinality(Servers)
       IN /\ newCommitIndex # commitIndex[s]
          /\ commitIndex' = [commitIndex EXCEPT ![s] = newCommitIndex]
    /\ UNCHANGED <<currentTerm, votedFor, log, state, nextIndex, matchIndex, votes, messages, electionTimeout, heartbeatTimeout>>

TimeoutTrigger(s) ==
    /\ electionTimeout' = [electionTimeout EXCEPT ![s] = TRUE]
    /\ UNCHANGED <<currentTerm, votedFor, log, state, commitIndex, nextIndex, matchIndex, votes, messages, heartbeatTimeout>>

HeartbeatTrigger(s) ==
    /\ heartbeatTimeout' = [heartbeatTimeout EXCEPT ![s] = TRUE]
    /\ UNCHANGED <<currentTerm, votedFor, log, state, commitIndex, nextIndex, matchIndex, votes, messages, electionTimeout>>

Next ==
    \/ \E s \in Servers : ElectionTimeout(s)
    \/ \E s \in Servers : HeartbeatTimeout(s)
    \/ \E m \in messages : HandleVoteRequest(m)
    \/ \E m \in messages : HandlePreVoteRequest(m)
    \/ \E m \in messages : HandleVoteResponse(m)
    \/ \E m \in messages : HandlePreVoteResponse(m)
    \/ \E m \in messages : HandleAppendEntries(m)
    \/ \E m \in messages : HandleAppendResponse(m)
    \/ \E m \in messages : HandleHeartbeat(m)
    \/ \E m \in messages : HandleHeartbeatResponse(m)
    \/ \E s \in Servers, entry \in 1..MaxTerm : ClientProposal(s, entry)
    \/ \E s, t \in Servers : AppendEntries(s, t)
    \/ \E s \in Servers : AdvanceCommitIndex(s)
    \/ \E s \in Servers : TimeoutTrigger(s)
    \/ \E s \in Servers : HeartbeatTrigger(s)

Spec == Init /\ [][Next]_vars

====