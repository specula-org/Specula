---- MODULE etcdraft ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Server, Key, Value, Client, Nil
VARIABLES
    state,
    currentTerm,
    votedFor,
    log,
    commitIndex,
    lastApplied,
    nextIndex,
    matchIndex,
    leaderId,
    kvState,
    uncommittedSize,
    pendingReadIndex,
    msgs,
    leadTransferee,
    electionElapsed,
    randomizedElectionTimeout

vars == <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, leaderId, kvState, uncommittedSize, pendingReadIndex, msgs, leadTransferee, electionElapsed, randomizedElectionTimeout>>

NodeState == {"Follower", "Candidate", "Leader"}
MessageType == {"AppendEntries", "AppendEntriesResp", "RequestVote", "RequestVoteResp", "PreVote", "PreVoteResp", "Snapshot", "Heartbeat", "HeartbeatResp", "TimeoutNow", "Propose", "ReadIndex", "Apply"}

Message == [type : MessageType, from : Server, to : Server, term : Nat, 
            prevLogIndex : Nat, prevLogTerm : Nat, entries : Seq([term : Nat, op : [type : {"Put", "Get", "Delete"}, key : Key, value : Value]]),
            leaderCommit : Nat, success : BOOLEAN, rejectHint : Nat, logTerm : Nat,
            snapshot : [metadata : [index : Nat, term : Nat]], ctx : Seq(Char),
            op : [type : {"Put", "Get", "Delete"}, key : Key, value : Value],
            voteGranted : BOOLEAN, matchIndex : Nat]

LogEntry == [term : Nat, op : [type : {"Put", "Get", "Delete"}, key : Key, value : Value]]

Init == 
    /\ state = [s \in Server |-> "Follower"]
    /\ currentTerm = [s \in Server |-> 0]
    /\ votedFor = [s \in Server |-> Nil]
    /\ log = [s \in Server |-> <<>>]
    /\ commitIndex = [s \in Server |-> 0]
    /\ lastApplied = [s \in Server |-> 0]
    /\ nextIndex = [s \in Server |-> [t \in Server |-> 1]]
    /\ matchIndex = [s \in Server |-> [t \in Server |-> 0]]
    /\ leaderId = [s \in Server |-> Nil]
    /\ kvState = [s \in Server |-> [k \in Key |-> Nil]]
    /\ uncommittedSize = [s \in Server |-> 0]
    /\ pendingReadIndex = [s \in Server |-> <<>>]
    /\ msgs = {}
    /\ leadTransferee = [s \in Server |-> Nil]
    /\ electionElapsed = [s \in Server |-> 0]
    /\ randomizedElectionTimeout = [s \in Server |-> 0]

Quorum(S) == { Q \in SUBSET S : Cardinality(Q) > Cardinality(S) \div 2 }

LastLogTerm(s) == 
    IF log[s] = <<>> THEN 0
    ELSE log[s][Len(log[s])].term

LastLogIndex(s) == Len(log[s])

IsLeader(s) == state[s] = "Leader"

IsCandidate(s) == state[s] = "Candidate"

IsFollower(s) == state[s] = "Follower"

CanVote(s) == 
    \/ votedFor[s] = Nil 
    \/ votedFor[s] = s

LogUpToDate(lastLogIndex, lastLogTerm, s) ==
    \/ lastLogTerm > LastLogTerm(s)
    \/ (lastLogTerm = LastLogTerm(s) /\ lastLogIndex >= LastLogIndex(s))

HandleRequestVote(s, m) ==
    /\ m.type = "RequestVote"
    /\ \/ m.term > currentTerm[s]
       \/ (m.term = currentTerm[s] /\ CanVote(s) /\ LogUpToDate(m.lastLogIndex, m.lastLogTerm, s))
    /\ currentTerm' = [currentTerm EXCEPT ![s] = m.term]
    /\ votedFor' = [votedFor EXCEPT ![s] = m.from]
    /\ msgs' = msgs \cup { [type |-> "RequestVoteResp", from |-> s, to |-> m.from, term |-> m.term, voteGranted |-> TRUE,
                            prevLogIndex |-> 0, prevLogTerm |-> 0, entries |-> <<>>, leaderCommit |-> 0, success |-> FALSE, 
                            rejectHint |-> 0, logTerm |-> 0, snapshot |-> [metadata |-> [index |-> 0, term |-> 0]], 
                            ctx |-> <<>>, op |-> [type |-> "Get", key |-> Nil, value |-> Nil], matchIndex |-> 0] }
    /\ UNCHANGED <<state, log, commitIndex, lastApplied, nextIndex, matchIndex, leaderId, kvState, uncommittedSize, pendingReadIndex, leadTransferee, electionElapsed, randomizedElectionTimeout>>

HandleAppendEntries(s, m) ==
    /\ m.type = "AppendEntries"
    /\ \/ m.term < currentTerm[s]
       \/ ~(m.prevLogIndex = 0 \/ (m.prevLogIndex <= Len(log[s]) /\ log[s][m.prevLogIndex].term = m.prevLogTerm))
    /\ msgs' = msgs \cup { [type |-> "AppendEntriesResp", from |-> s, to |-> m.from, term |-> currentTerm[s], success |-> FALSE, rejectHint |-> LastLogIndex(s),
                            prevLogIndex |-> 0, prevLogTerm |-> 0, entries |-> <<>>, leaderCommit |-> 0, logTerm |-> 0, 
                            snapshot |-> [metadata |-> [index |-> 0, term |-> 0]], ctx |-> <<>>, 
                            op |-> [type |-> "Get", key |-> Nil, value |-> Nil], voteGranted |-> FALSE, matchIndex |-> 0] }
    /\ UNCHANGED vars

HandleAppendEntriesSuccess(s, m) ==
    /\ m.type = "AppendEntries"
    /\ m.term >= currentTerm[s]
    /\ (m.prevLogIndex = 0 \/ (m.prevLogIndex <= Len(log[s]) /\ log[s][m.prevLogIndex].term = m.prevLogTerm))
    /\ \/ m.term > currentTerm[s]
       \/ leaderId[s] = Nil
    /\ leaderId' = [leaderId EXCEPT ![s] = m.from]
    /\ currentTerm' = [currentTerm EXCEPT ![s] = m.term]
    /\ electionElapsed' = [electionElapsed EXCEPT ![s] = 0]
    /\ LET newLog == IF m.prevLogIndex = 0 
                    THEN m.entries 
                    ELSE SubSeq(log[s], 1, m.prevLogIndex) \o m.entries
           newLogLen == Len(newLog)
        IN
        /\ log' = [log EXCEPT ![s] = newLog]
        /\ commitIndex' = [commitIndex EXCEPT ![s] = Min(m.leaderCommit, newLogLen)]
        /\ msgs' = msgs \cup { [type |-> "AppendEntriesResp", from |-> s, to |-> m.from, term |-> m.term, success |-> TRUE, matchIndex |-> newLogLen,
                               prevLogIndex |-> 0, prevLogTerm |-> 0, entries |-> <<>>, leaderCommit |-> 0, rejectHint |-> 0, logTerm |-> 0,
                               snapshot |-> [metadata |-> [index |-> 0, term |-> 0]], ctx |-> <<>>, 
                               op |-> [type |-> "Get", key |-> Nil, value |-> Nil], voteGranted |-> FALSE] }
    /\ UNCHANGED <<state, votedFor, lastApplied, nextIndex, matchIndex, kvState, uncommittedSize, pendingReadIndex, leadTransferee, randomizedElectionTimeout>>

LeaderAppendEntry(s, op) ==
    /\ IsLeader(s)
    /\ LET newEntry == [term |-> currentTerm[s], op |-> op]
           newLog == log[s] \o <<newEntry>>
           newLogLen == Len(newLog)
        IN
        /\ log' = [log EXCEPT ![s] = newLog]
        /\ nextIndex' = [nextIndex EXCEPT ![s][s] = newLogLen + 1]
        /\ matchIndex' = [matchIndex EXCEPT ![s][s] = newLogLen]
        /\ msgs' = msgs \cup { [type |-> "AppendEntries", from |-> s, to |-> t, term |-> currentTerm[s], 
                          prevLogIndex |-> nextIndex[s][t] - 1, 
                          prevLogTerm |-> IF nextIndex[s][t] > 1 THEN log[s][nextIndex[s][t] - 1].term ELSE 0,
                          entries |-> IF nextIndex[s][t] > Len(log[s]) THEN <<>> ELSE SubSeq(log[s], nextIndex[s][t], Len(log[s])), 
                          leaderCommit |-> commitIndex[s], success |-> FALSE, rejectHint |-> 0, logTerm |-> 0,
                          snapshot |-> [metadata |-> [index |-> 0, term |-> 0]], ctx |-> <<>>, 
                          op |-> [type |-> "Get", key |-> Nil, value |-> Nil], voteGranted |-> FALSE, matchIndex |-> 0] : t \in Server \ {s} }
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, lastApplied, leaderId, kvState, uncommittedSize, pendingReadIndex, leadTransferee, electionElapsed, randomizedElectionTimeout>>

CommitEntry(s) ==
    /\ commitIndex[s] > lastApplied[s]
    /\ lastApplied' = [lastApplied EXCEPT ![s] = lastApplied[s] + 1]
    /\ LET entry == log[s][lastApplied[s] + 1]
           newKvState == IF entry.op.type = "Put" 
                         THEN [kvState[s] EXCEPT ![entry.op.key] = entry.op.value]
                         ELSE IF entry.op.type = "Delete" 
                              THEN [kvState[s] EXCEPT ![entry.op.key] = Nil]
                              ELSE kvState[s]
        IN
        /\ kvState' = [kvState EXCEPT ![s] = newKvState]
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, leaderId, uncommittedSize, pendingReadIndex, msgs, leadTransferee, electionElapsed, randomizedElectionTimeout>>

BecomeLeader(s) ==
    /\ IsCandidate(s)
    /\ LET votes == { t \in Server : \E m \in msgs : m.type = "RequestVoteResp" /\ m.to = s /\ m.term = currentTerm[s] /\ m.voteGranted }
        IN \E Q \in Quorum(Server) : Q \subseteq (votes \cup {s})
    /\ state' = [state EXCEPT ![s] = "Leader"]
    /\ leaderId' = [leaderId EXCEPT ![s] = s]
    /\ nextIndex' = [nextIndex EXCEPT ![s] = [t \in Server |-> Len(log[s]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![s] = [t \in Server |-> 0]]
    /\ msgs' = msgs \cup { [type |-> "AppendEntries", from |-> s, to |-> t, term |-> currentTerm[s], 
                          prevLogIndex |-> LastLogIndex(s), prevLogTerm |-> LastLogTerm(s),
                          entries |-> <<>>, leaderCommit |-> commitIndex[s], success |-> FALSE, rejectHint |-> 0, logTerm |-> 0,
                          snapshot |-> [metadata |-> [index |-> 0, term |-> 0]], ctx |-> <<>>, 
                          op |-> [type |-> "Get", key |-> Nil, value |-> Nil], voteGranted |-> FALSE, matchIndex |-> 0] : t \in Server \ {s} }
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, lastApplied, kvState, uncommittedSize, pendingReadIndex, leadTransferee, electionElapsed, randomizedElectionTimeout>>

StartElection(s) ==
    /\ \/ IsFollower(s) \/ IsCandidate(s)
    /\ electionElapsed[s] >= randomizedElectionTimeout[s]
    /\ state' = [state EXCEPT ![s] = "Candidate"]
    /\ currentTerm' = [currentTerm EXCEPT ![s] = currentTerm[s] + 1]
    /\ votedFor' = [votedFor EXCEPT ![s] = s]
    /\ electionElapsed' = [electionElapsed EXCEPT ![s] = 0]
    /\ randomizedElectionTimeout' = randomizedElectionTimeout
    /\ msgs' = msgs \cup { [type |-> "RequestVote", from |-> s, to |-> t, term |-> currentTerm[s] + 1, 
                          lastLogIndex |-> LastLogIndex(s), lastLogTerm |-> LastLogTerm(s),
                          prevLogIndex |-> 0, prevLogTerm |-> 0, entries |-> <<>>, leaderCommit |-> 0, success |-> FALSE, 
                          rejectHint |-> 0, logTerm |-> 0, snapshot |-> [metadata |-> [index |-> 0, term |-> 0]], 
                          ctx |-> <<>>, op |-> [type |-> "Get", key |-> Nil, value |-> Nil], voteGranted |-> FALSE, matchIndex |-> 0] : t \in Server \ {s} }
    /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex, leaderId, kvState, uncommittedSize, pendingReadIndex, leadTransferee>>

HandleReadIndex(s, m) ==
    /\ m.type = "ReadIndex"
    /\ IsLeader(s)
    /\ pendingReadIndex' = [pendingReadIndex EXCEPT ![s] = pendingReadIndex[s] \o <<m>>]
    /\ msgs' = msgs \cup { [type |-> "Heartbeat", from |-> s, to |-> t, term |-> currentTerm[s], ctx |-> m.ctx,
                          prevLogIndex |-> 0, prevLogTerm |-> 0, entries |-> <<>>, leaderCommit |-> 0, success |-> FALSE, 
                          rejectHint |-> 0, logTerm |-> 0, snapshot |-> [metadata |-> [index |-> 0, term |-> 0]], 
                          op |-> [type |-> "Get", key |-> Nil, value |-> Nil], voteGranted |-> FALSE, matchIndex |-> 0] : t \in Server \ {s} }
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, leaderId, kvState, uncommittedSize, leadTransferee, electionElapsed, randomizedElectionTimeout>>

RespondReadIndex(s) ==
    /\ IsLeader(s)
    /\ pendingReadIndex[s] /= <<>>
    /\ \E Q \in Quorum(Server) : 
          \A t \in Q : \E m \in msgs : m.type = "HeartbeatResp" /\ m.to = s /\ m.term = currentTerm[s] 
    /\ LET readReq == HEAD(pendingReadIndex[s])
           key == readReq.op.key
           value == kvState[s][key]
        IN
        /\ msgs' = msgs \cup { [type |-> "Apply", from |-> s, to |-> readReq.from, value |-> value,
                          prevLogIndex |-> 0, prevLogTerm |-> 0, entries |-> <<>>, leaderCommit |-> 0, success |-> FALSE, 
                          rejectHint |-> 0, logTerm |-> 0, snapshot |-> [metadata |-> [index |-> 0, term |-> 0]], 
                          ctx |-> <<>>, op |-> [type |-> "Get", key |-> Nil, value |-> Nil], voteGranted |-> FALSE, matchIndex |-> 0] }
        /\ pendingReadIndex' = [pendingReadIndex EXCEPT ![s] = Tail(pendingReadIndex[s])]
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex, matchIndex, leaderId, kvState, uncommittedSize, leadTransferee, electionElapsed, randomizedElectionTimeout>>

Next ==
    \/ \E s \in Server : BecomeLeader(s)
    \/ \E s \in Server : StartElection(s)
    \/ \E s \in Server : CommitEntry(s)
    \/ \E s \in Server : RespondReadIndex(s)
    \/ \E m \in msgs : 
        \/ \E s \in Server : HandleRequestVote(s, m)
        \/ \E s \in Server : HandleAppendEntries(s, m)
        \/ \E s \in Server : HandleAppendEntriesSuccess(s, m)
        \/ \E s \in Server : HandleReadIndex(s, m)
    \/ \E s \in Server, op \in [type : {"Put", "Delete"}, key : Key, value : Value] : 
        LeaderAppendEntry(s, op)

TypeInvariant ==
    /\ state \in [Server -> NodeState]
    /\ currentTerm \in [Server -> Nat]
    /\ votedFor \in [Server -> Server \cup {Nil}]
    /\ log \in [Server -> Seq(LogEntry)]
    /\ commitIndex \in [Server -> Nat]
    /\ lastApplied \in [Server -> Nat]
    /\ nextIndex \in [Server -> [Server -> Nat]]
    /\ matchIndex \in [Server -> [Server -> Nat]]
    /\ leaderId \in [Server -> Server \cup {Nil}]
    /\ kvState \in [Server -> [Key -> Value \cup {Nil}]]
    /\ uncommittedSize \in [Server -> Nat]
    /\ pendingReadIndex \in [Server -> Seq(Message)]
    /\ msgs \subseteq [type : MessageType, from : Server, to : Server, term : Nat, 
                      prevLogIndex : Nat, prevLogTerm : Nat, entries : Seq(LogEntry),
                      leaderCommit : Nat, success : BOOLEAN, rejectHint : Nat, logTerm : Nat,
                      snapshot : [metadata : [index : Nat, term : Nat]], ctx : Seq(Char),
                      op : [type : {"Put", "Get", "Delete"}, key : Key, value : Value],
                      voteGranted : BOOLEAN, matchIndex : Nat]
    /\ leadTransferee \in [Server -> Server \cup {Nil}]
    /\ electionElapsed \in [Server -> Nat]
    /\ randomizedElectionTimeout \in [Server -> Nat]

Invariant ==
    \A s1, s2 \in Server : 
        (state[s1] = "Leader" /\ state[s2] = "Leader" /\ currentTerm[s1] = currentTerm[s2]) => s1 = s2

Spec == Init /\ [][Next]_vars

====