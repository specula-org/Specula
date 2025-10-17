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

None == 0
StateFollower == "Follower"
StateCandidate == "Candidate" 
StateLeader == "Leader"
StatePreCandidate == "PreCandidate"

MsgHup == "MsgHup"
MsgVote == "MsgVote"
MsgVoteResp == "MsgVoteResp"
MsgPreVote == "MsgPreVote"
MsgPreVoteResp == "MsgPreVoteResp"
MsgApp == "MsgApp"
MsgAppResp == "MsgAppResp"
MsgHeartbeat == "MsgHeartbeat"
MsgHeartbeatResp == "MsgHeartbeatResp"
MsgProp == "MsgProp"

Message(mtype, mfrom, mto, mterm, mlogTerm, mindex, mentries, mcommit, mvoteGranted, mreject) ==
    [type |-> mtype, from |-> mfrom, to |-> mto, term |-> mterm, 
     logTerm |-> mlogTerm, index |-> mindex, entries |-> mentries,
     commit |-> mcommit, voteGranted |-> mvoteGranted, reject |-> mreject]

Entry(term, index, data) == [term |-> term, index |-> index, data |-> data]

Init ==
    /\ currentTerm = [i \in Servers |-> 1]
    /\ votedFor = [i \in Servers |-> None]
    /\ log = [i \in Servers |-> <<>>]
    /\ state = [i \in Servers |-> StateFollower]
    /\ commitIndex = [i \in Servers |-> 0]
    /\ nextIndex = [i \in Servers |-> [j \in Servers |-> 1]]
    /\ matchIndex = [i \in Servers |-> [j \in Servers |-> 0]]
    /\ votes = [i \in Servers |-> {}]
    /\ messages = {}
    /\ electionTimeout = [i \in Servers |-> FALSE]
    /\ heartbeatTimeout = [i \in Servers |-> FALSE]

Send(m) == messages' = messages \cup {m}

Reply(response, request) ==
    Send([type |-> response.type, from |-> response.from, to |-> response.to,
          term |-> response.term, logTerm |-> response.logTerm, index |-> response.index,
          entries |-> response.entries, commit |-> response.commit, 
          voteGranted |-> response.voteGranted, reject |-> response.reject])

Discard(m) == messages' = messages \ {m}

LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)].term
LastIndex(xlog) == Len(xlog)

IsUpToDate(i, j) ==
    \/ LastTerm(log[i]) > LastTerm(log[j])
    \/ /\ LastTerm(log[i]) = LastTerm(log[j])
       /\ LastIndex(log[i]) >= LastIndex(log[j])

CanVote(i, j, logTerm, logIndex) ==
    /\ \/ votedFor[i] = None
       \/ votedFor[i] = j
    /\ \/ logTerm > LastTerm(log[i])
       \/ /\ logTerm = LastTerm(log[i])
          /\ logIndex >= LastIndex(log[i])

BecomeFollower(i, term) ==
    /\ currentTerm' = [currentTerm EXCEPT ![i] = term]
    /\ state' = [state EXCEPT ![i] = StateFollower]
    /\ votedFor' = [votedFor EXCEPT ![i] = None]
    /\ electionTimeout' = [electionTimeout EXCEPT ![i] = FALSE]
    /\ heartbeatTimeout' = [heartbeatTimeout EXCEPT ![i] = FALSE]

BecomePreCandidate(i) ==
    /\ state' = [state EXCEPT ![i] = StatePreCandidate]
    /\ votes' = [votes EXCEPT ![i] = {}]
    /\ electionTimeout' = [electionTimeout EXCEPT ![i] = FALSE]

BecomeCandidate(i) ==
    /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
    /\ state' = [state EXCEPT ![i] = StateCandidate]
    /\ votedFor' = [votedFor EXCEPT ![i] = i]
    /\ votes' = [votes EXCEPT ![i] = {i}]
    /\ electionTimeout' = [electionTimeout EXCEPT ![i] = FALSE]

BecomeLeader(i) ==
    /\ state' = [state EXCEPT ![i] = StateLeader]
    /\ nextIndex' = [nextIndex EXCEPT ![i] = [j \in Servers |-> LastIndex(log[i]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![i] = [j \in Servers |-> 0]]
    /\ heartbeatTimeout' = [heartbeatTimeout EXCEPT ![i] = FALSE]

ElectionTimeout(i) ==
    /\ state[i] \in {StateFollower, StateCandidate, StatePreCandidate}
    /\ electionTimeout[i] = TRUE
    /\ electionTimeout' = [electionTimeout EXCEPT ![i] = FALSE]
    /\ IF state[i] = StateFollower
       THEN /\ BecomePreCandidate(i)
            /\ \A j \in Servers \ {i} :
                Send(Message(MsgPreVote, i, j, currentTerm[i] + 1, LastTerm(log[i]), LastIndex(log[i]), <<>>, 0, FALSE, FALSE))
            /\ UNCHANGED <<votedFor, log, commitIndex, nextIndex, matchIndex, heartbeatTimeout>>
       ELSE IF state[i] = StatePreCandidate
            THEN /\ BecomeCandidate(i)
                 /\ \A j \in Servers \ {i} :
                     Send(Message(MsgVote, i, j, currentTerm'[i], LastTerm(log[i]), LastIndex(log[i]), <<>>, 0, FALSE, FALSE))
                 /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex, heartbeatTimeout>>
            ELSE /\ BecomeCandidate(i)
                 /\ \A j \in Servers \ {i} :
                     Send(Message(MsgVote, i, j, currentTerm'[i], LastTerm(log[i]), LastIndex(log[i]), <<>>, 0, FALSE, FALSE))
                 /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex, heartbeatTimeout>>

HeartbeatTimeout(i) ==
    /\ state[i] = StateLeader
    /\ heartbeatTimeout[i] = TRUE
    /\ heartbeatTimeout' = [heartbeatTimeout EXCEPT ![i] = FALSE]
    /\ \A j \in Servers \ {i} :
        Send(Message(MsgHeartbeat, i, j, currentTerm[i], 0, 0, <<>>, commitIndex[i], FALSE, FALSE))
    /\ UNCHANGED <<currentTerm, votedFor, log, state, commitIndex, nextIndex, matchIndex, votes, electionTimeout>>

HandleMessage(m) ==
    LET i == m.to IN
    /\ m \in messages
    /\ Discard(m)
    /\ \/ /\ m.term > currentTerm[i]
          /\ BecomeFollower(i, m.term)
          /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex, votes, heartbeatTimeout>>
       \/ /\ m.term = currentTerm[i]
          /\ HandleCurrentTermMessage(m)
       \/ /\ m.term < currentTerm[i]
          /\ UNCHANGED <<currentTerm, votedFor, log, state, commitIndex, nextIndex, matchIndex, votes, electionTimeout, heartbeatTimeout>>

HandleCurrentTermMessage(m) ==
    LET i == m.to IN
    \/ /\ m.type = MsgVote
       /\ CanVote(i, m.from, m.logTerm, m.index)
       /\ votedFor' = [votedFor EXCEPT ![i] = m.from]
       /\ Reply(Message(MsgVoteResp, i, m.from, currentTerm[i], 0, 0, <<>>, 0, TRUE, FALSE), m)
       /\ UNCHANGED <<currentTerm, log, state, commitIndex, nextIndex, matchIndex, votes, electionTimeout, heartbeatTimeout>>
    \/ /\ m.type = MsgVote
       /\ ~CanVote(i, m.from, m.logTerm, m.index)
       /\ Reply(Message(MsgVoteResp, i, m.from, currentTerm[i], 0, 0, <<>>, 0, FALSE, TRUE), m)
       /\ UNCHANGED <<currentTerm, votedFor, log, state, commitIndex, nextIndex, matchIndex, votes, electionTimeout, heartbeatTimeout>>
    \/ /\ m.type = MsgPreVote
       /\ CanVote(i, m.from, m.logTerm, m.index)
       /\ Reply(Message(MsgPreVoteResp, i, m.from, currentTerm[i], 0, 0, <<>>, 0, TRUE, FALSE), m)
       /\ UNCHANGED <<currentTerm, votedFor, log, state, commitIndex, nextIndex, matchIndex, votes, electionTimeout, heartbeatTimeout>>
    \/ /\ m.type = MsgPreVote
       /\ ~CanVote(i, m.from, m.logTerm, m.index)
       /\ Reply(Message(MsgPreVoteResp, i, m.from, currentTerm[i], 0, 0, <<>>, 0, FALSE, TRUE), m)
       /\ UNCHANGED <<currentTerm, votedFor, log, state, commitIndex, nextIndex, matchIndex, votes, electionTimeout, heartbeatTimeout>>
    \/ /\ m.type = MsgVoteResp
       /\ state[i] = StateCandidate
       /\ HandleVoteResponse(m)
    \/ /\ m.type = MsgPreVoteResp
       /\ state[i] = StatePreCandidate
       /\ HandlePreVoteResponse(m)
    \/ /\ m.type = MsgApp
       /\ HandleAppendEntries(m)
    \/ /\ m.type = MsgAppResp
       /\ state[i] = StateLeader
       /\ HandleAppendResponse(m)
    \/ /\ m.type = MsgHeartbeat
       /\ state[i] = StateFollower
       /\ electionTimeout' = [electionTimeout EXCEPT ![i] = FALSE]
       /\ commitIndex' = [commitIndex EXCEPT ![i] = m.commit]
       /\ Reply(Message(MsgHeartbeatResp, i, m.from, currentTerm[i], 0, 0, <<>>, 0, FALSE, FALSE), m)
       /\ UNCHANGED <<currentTerm, votedFor, log, state, nextIndex, matchIndex, votes, heartbeatTimeout>>
    \/ /\ m.type = MsgHeartbeatResp
       /\ state[i] = StateLeader
       /\ UNCHANGED <<currentTerm, votedFor, log, state, commitIndex, nextIndex, matchIndex, votes, electionTimeout, heartbeatTimeout>>
    \/ /\ m.type = MsgProp
       /\ state[i] = StateLeader
       /\ HandleProposal(m)

HandleVoteResponse(m) ==
    LET i == m.to IN
    /\ IF m.voteGranted
       THEN votes' = [votes EXCEPT ![i] = votes[i] \cup {m.from}]
       ELSE UNCHANGED votes
    /\ IF Cardinality(votes'[i]) * 2 > Cardinality(Servers)
       THEN BecomeLeader(i)
       ELSE UNCHANGED <<currentTerm, state, nextIndex, matchIndex, heartbeatTimeout>>
    /\ UNCHANGED <<votedFor, log, commitIndex, electionTimeout>>

HandlePreVoteResponse(m) ==
    LET i == m.to IN
    /\ IF m.voteGranted
       THEN votes' = [votes EXCEPT ![i] = votes[i] \cup {m.from}]
       ELSE UNCHANGED votes
    /\ IF Cardinality(votes'[i]) * 2 > Cardinality(Servers)
       THEN /\ BecomeCandidate(i)
            /\ \A j \in Servers \ {i} :
                Send(Message(MsgVote, i, j, currentTerm'[i], LastTerm(log[i]), LastIndex(log[i]), <<>>, 0, FALSE, FALSE))
            /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex, heartbeatTimeout>>
       ELSE UNCHANGED <<currentTerm, votedFor, log, state, commitIndex, nextIndex, matchIndex, heartbeatTimeout>>
    /\ UNCHANGED electionTimeout

HandleAppendEntries(m) ==
    LET i == m.to
        logOk == \/ m.index = 0
                 \/ /\ m.index > 0
                    /\ m.index <= Len(log[i])
                    /\ log[i][m.index].term = m.logTerm
    IN
    /\ electionTimeout' = [electionTimeout EXCEPT ![i] = FALSE]
    /\ IF logOk
       THEN /\ log' = [log EXCEPT ![i] = SubSeq(log[i], 1, m.index) \o m.entries]
            /\ commitIndex' = [commitIndex EXCEPT ![i] = m.commit]
            /\ Reply(Message(MsgAppResp, i, m.from, currentTerm[i], 0, m.index + Len(m.entries), <<>>, 0, FALSE, FALSE), m)
       ELSE /\ Reply(Message(MsgAppResp, i, m.from, currentTerm[i], 0, 0, <<>>, 0, FALSE, TRUE), m)
            /\ UNCHANGED <<log, commitIndex>>
    /\ UNCHANGED <<currentTerm, votedFor, state, nextIndex, matchIndex, votes, heartbeatTimeout>>

HandleAppendResponse(m) ==
    LET i == m.to IN
    /\ IF m.reject
       THEN /\ nextIndex' = [nextIndex EXCEPT ![i][m.from] = Max(nextIndex[i][m.from] - 1, 1)]
            /\ UNCHANGED matchIndex
       ELSE /\ nextIndex' = [nextIndex EXCEPT ![i][m.from] = m.index + 1]
            /\ matchIndex' = [matchIndex EXCEPT ![i][m.from] = m.index]
    /\ UNCHANGED <<currentTerm, votedFor, log, state, commitIndex, votes, electionTimeout, heartbeatTimeout>>

HandleProposal(m) ==
    LET i == m.to
        newEntry == Entry(currentTerm[i], Len(log[i]) + 1, m.entries[1].data)
    IN
    /\ Len(log[i]) < MaxLogLen
    /\ log' = [log EXCEPT ![i] = Append(log[i], newEntry)]
    /\ \A j \in Servers \ {i} :
        Send(Message(MsgApp, i, j, currentTerm[i], LastTerm(log[i]), LastIndex(log[i]), <<newEntry>>, commitIndex[i], FALSE, FALSE))
    /\ UNCHANGED <<currentTerm, votedFor, state, commitIndex, nextIndex, matchIndex, votes, electionTimeout, heartbeatTimeout>>

ClientRequest(i, data) ==
    /\ state[i] = StateLeader
    /\ Send(Message(MsgProp, None, i, 0, 0, 0, <<Entry(0, 0, data)>>, 0, FALSE, FALSE))
    /\ UNCHANGED vars

TimeoutTick(i) ==
    \/ /\ electionTimeout' = [electionTimeout EXCEPT ![i] = TRUE]
       /\ UNCHANGED <<currentTerm, votedFor, log, state, commitIndex, nextIndex, matchIndex, votes, messages, heartbeatTimeout>>
    \/ /\ heartbeatTimeout' = [heartbeatTimeout EXCEPT ![i] = TRUE]
       /\ UNCHANGED <<currentTerm, votedFor, log, state, commitIndex, nextIndex, matchIndex, votes, messages, electionTimeout>>

Next ==
    \/ \E i \in Servers : ElectionTimeout(i)
    \/ \E i \in Servers : HeartbeatTimeout(i)
    \/ \E m \in messages : HandleMessage(m)
    \/ \E i \in Servers, data \in 1..3 : ClientRequest(i, data)
    \/ \E i \in Servers : TimeoutTick(i)

Spec == Init /\ [][Next]_vars

====