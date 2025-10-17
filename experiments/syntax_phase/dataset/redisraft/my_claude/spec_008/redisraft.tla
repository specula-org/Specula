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
    votingNodes

vars == <<currentTerm, state, votedFor, log, commitIndex, lastApplied,
          nextIndex, matchIndex, electionTimeout, heartbeatTimeout,
          messages, votesGranted, snapshotLastIndex, snapshotLastTerm,
          configChangeInProgress, votingNodes>>

States == {"FOLLOWER", "PRECANDIDATE", "CANDIDATE", "LEADER"}

TypeOK ==
    /\ currentTerm \in [Servers -> 0..MaxTerm]
    /\ state \in [Servers -> States]
    /\ votedFor \in [Servers -> Servers \cup {Nil}]
    /\ log \in [Servers -> Seq([term: 0..MaxTerm, type: STRING, data: STRING])]
    /\ commitIndex \in [Servers -> Nat]
    /\ lastApplied \in [Servers -> Nat]
    /\ nextIndex \in [Servers -> [Servers -> Nat]]
    /\ matchIndex \in [Servers -> [Servers -> Nat]]
    /\ electionTimeout \in [Servers -> BOOLEAN]
    /\ heartbeatTimeout \in [Servers -> BOOLEAN]
    /\ messages \subseteq (
        [type: {"RequestVote"}, term: 0..MaxTerm, candidateId: Servers,
         lastLogIndex: Nat, lastLogTerm: 0..MaxTerm, prevote: BOOLEAN] \cup
        [type: {"RequestVoteResponse"}, term: 0..MaxTerm, voteGranted: BOOLEAN,
         prevote: BOOLEAN, from: Servers] \cup
        [type: {"AppendEntries"}, term: 0..MaxTerm, leaderId: Servers,
         prevLogIndex: Nat, prevLogTerm: 0..MaxTerm, entries: Seq([term: 0..MaxTerm, type: STRING, data: STRING]),
         leaderCommit: Nat] \cup
        [type: {"AppendEntriesResponse"}, term: 0..MaxTerm, success: BOOLEAN,
         matchIndex: Nat, from: Servers]
    )
    /\ votesGranted \in [Servers -> SUBSET Servers]
    /\ snapshotLastIndex \in [Servers -> Nat]
    /\ snapshotLastTerm \in [Servers -> 0..MaxTerm]
    /\ configChangeInProgress \in [Servers -> BOOLEAN]
    /\ votingNodes \subseteq Servers

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
    /\ votingNodes = Servers

LastLogIndex(s) == Len(log[s]) + snapshotLastIndex[s]

LastLogTerm(s) ==
    IF Len(log[s]) = 0
    THEN snapshotLastTerm[s]
    ELSE log[s][Len(log[s])].term

GetLogTerm(s, index) ==
    IF index = 0
    THEN 0
    ELSE IF index <= snapshotLastIndex[s]
         THEN snapshotLastTerm[s]
         ELSE log[s][index - snapshotLastIndex[s]].term

IsQuorum(servers) == Cardinality(servers) * 2 > Cardinality(votingNodes)

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
    /\ LET requestVoteMsg == [type |-> "RequestVote",
                              term |-> currentTerm[s] + 1,
                              candidateId |-> s,
                              lastLogIndex |-> LastLogIndex(s),
                              lastLogTerm |-> LastLogTerm(s),
                              prevote |-> TRUE]
       IN messages' = messages \cup {requestVoteMsg}
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, lastApplied,
                   nextIndex, matchIndex, heartbeatTimeout, snapshotLastIndex,
                   snapshotLastTerm, configChangeInProgress, votingNodes>>

BecomeCandidate(s) ==
    /\ state[s] \in {"FOLLOWER", "PRECANDIDATE"}
    /\ \/ /\ state[s] = "FOLLOWER"
          /\ electionTimeout[s] = TRUE
       \/ /\ state[s] = "PRECANDIDATE"
          /\ IsQuorum(votesGranted[s])
    /\ currentTerm' = [currentTerm EXCEPT ![s] = currentTerm[s] + 1]
    /\ state' = [state EXCEPT ![s] = "CANDIDATE"]
    /\ votedFor' = [votedFor EXCEPT ![s] = s]
    /\ votesGranted' = [votesGranted EXCEPT ![s] = {s}]
    /\ electionTimeout' = [electionTimeout EXCEPT ![s] = FALSE]
    /\ LET requestVoteMsg == [type |-> "RequestVote",
                              term |-> currentTerm[s] + 1,
                              candidateId |-> s,
                              lastLogIndex |-> LastLogIndex(s),
                              lastLogTerm |-> LastLogTerm(s),
                              prevote |-> FALSE]
       IN messages' = messages \cup {requestVoteMsg}
    /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex,
                   heartbeatTimeout, snapshotLastIndex, snapshotLastTerm,
                   configChangeInProgress, votingNodes>>

BecomeLeader(s) ==
    /\ state[s] = "CANDIDATE"
    /\ IsQuorum(votesGranted[s])
    /\ state' = [state EXCEPT ![s] = "LEADER"]
    /\ nextIndex' = [nextIndex EXCEPT ![s] = [t \in Servers |-> LastLogIndex(s) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![s] = [t \in Servers |-> 0]]
    /\ heartbeatTimeout' = [heartbeatTimeout EXCEPT ![s] = TRUE]
    /\ LET noopEntry == [term |-> currentTerm[s], type |-> "NOOP", data |-> ""]
       IN log' = [log EXCEPT ![s] = Append(log[s], noopEntry)]
    /\ UNCHANGED <<currentTerm, votedFor, commitIndex, lastApplied,
                   electionTimeout, messages, votesGranted, snapshotLastIndex,
                   snapshotLastTerm, configChangeInProgress, votingNodes>>

ElectionTimeout(s) ==
    /\ state[s] = "FOLLOWER"
    /\ electionTimeout' = [electionTimeout EXCEPT ![s] = TRUE]
    /\ UNCHANGED <<currentTerm, state, votedFor, log, commitIndex, lastApplied,
                   nextIndex, matchIndex, heartbeatTimeout, messages,
                   votesGranted, snapshotLastIndex, snapshotLastTerm,
                   configChangeInProgress, votingNodes>>

HeartbeatTimeout(s) ==
    /\ state[s] = "LEADER"
    /\ heartbeatTimeout' = [heartbeatTimeout EXCEPT ![s] = TRUE]
    /\ UNCHANGED <<currentTerm, state, votedFor, log, commitIndex, lastApplied,
                   nextIndex, matchIndex, electionTimeout, messages,
                   votesGranted, snapshotLastIndex, snapshotLastTerm,
                   configChangeInProgress, votingNodes>>

SendAppendEntries(s, t) ==
    /\ state[s] = "LEADER"
    /\ heartbeatTimeout[s] = TRUE
    /\ t \in Servers
    /\ t # s
    /\ LET prevLogIndex == nextIndex[s][t] - 1
           prevLogTerm == GetLogTerm(s, prevLogIndex)
           entries == IF nextIndex[s][t] <= LastLogIndex(s)
                      THEN SubSeq(log[s], nextIndex[s][t] - snapshotLastIndex[s],
                                  Len(log[s]))
                      ELSE <<>>
           appendMsg == [type |-> "AppendEntries",
                         term |-> currentTerm[s],
                         leaderId |-> s,
                         prevLogIndex |-> prevLogIndex,
                         prevLogTerm |-> prevLogTerm,
                         entries |-> entries,
                         leaderCommit |-> commitIndex[s]]
       IN messages' = messages \cup {appendMsg}
    /\ UNCHANGED <<currentTerm, state, votedFor, log, commitIndex, lastApplied,
                   nextIndex, matchIndex, electionTimeout, heartbeatTimeout,
                   votesGranted, snapshotLastIndex, snapshotLastTerm,
                   configChangeInProgress, votingNodes>>

SendHeartbeat(s) ==
    /\ state[s] = "LEADER"
    /\ heartbeatTimeout[s] = TRUE
    /\ heartbeatTimeout' = [heartbeatTimeout EXCEPT ![s] = FALSE]
    /\ \A t \in Servers \ {s} : SendAppendEntries(s, t)

RecvRequestVote(s, m) ==
    /\ m.type = "RequestVote"
    /\ LET grant == /\ m.term >= currentTerm[s]
                    /\ \/ votedFor[s] = Nil
                       \/ votedFor[s] = m.candidateId
                    /\ \/ m.lastLogTerm > LastLogTerm(s)
                       \/ /\ m.lastLogTerm = LastLogTerm(s)
                          /\ m.lastLogIndex >= LastLogIndex(s)
       IN /\ IF m.term > currentTerm[s]
             THEN BecomeFollower(s, m.term)
             ELSE UNCHANGED <<currentTerm, state, votedFor, electionTimeout,
                              heartbeatTimeout, votesGranted>>
          /\ IF grant /\ ~m.prevote
             THEN votedFor' = [votedFor EXCEPT ![s] = m.candidateId]
             ELSE UNCHANGED votedFor
          /\ messages' = (messages \ {m}) \cup
                         {[type |-> "RequestVoteResponse",
                           term |-> currentTerm'[s],
                           voteGranted |-> grant,
                           prevote |-> m.prevote,
                           from |-> s]}
          /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex,
                         snapshotLastIndex, snapshotLastTerm,
                         configChangeInProgress, votingNodes>>

RecvRequestVoteResponse(s, m) ==
    /\ m.type = "RequestVoteResponse"
    /\ m.from # s
    /\ IF m.term > currentTerm[s]
       THEN BecomeFollower(s, m.term) /\ messages' = messages \ {m}
       ELSE /\ IF m.voteGranted
               THEN votesGranted' = [votesGranted EXCEPT ![s] = votesGranted[s] \cup {m.from}]
               ELSE UNCHANGED votesGranted
            /\ messages' = messages \ {m}
            /\ UNCHANGED <<currentTerm, state, votedFor, log, commitIndex,
                           lastApplied, nextIndex, matchIndex, electionTimeout,
                           heartbeatTimeout, snapshotLastIndex, snapshotLastTerm,
                           configChangeInProgress, votingNodes>>

RecvAppendEntries(s, m) ==
    /\ m.type = "AppendEntries"
    /\ LET success == /\ m.term >= currentTerm[s]
                      /\ \/ m.prevLogIndex = 0
                         \/ /\ m.prevLogIndex <= LastLogIndex(s)
                            /\ GetLogTerm(s, m.prevLogIndex) = m.prevLogTerm
       IN /\ IF m.term > currentTerm[s]
             THEN BecomeFollower(s, m.term)
             ELSE /\ IF m.term = currentTerm[s] /\ state[s] # "FOLLOWER"
                     THEN BecomeFollower(s, m.term)
                     ELSE UNCHANGED <<currentTerm, state, votedFor,
                                      electionTimeout, heartbeatTimeout, votesGranted>>
          /\ IF success
             THEN /\ log' = [log EXCEPT ![s] = 
                             SubSeq(log[s], 1, m.prevLogIndex - snapshotLastIndex[s]) \o m.entries]
                  /\ commitIndex' = [commitIndex EXCEPT ![s] = 
                                     IF m.leaderCommit > commitIndex[s]
                                     THEN Min(m.leaderCommit, LastLogIndex(s))
                                     ELSE commitIndex[s]]
             ELSE UNCHANGED <<log, commitIndex>>
          /\ messages' = (messages \ {m}) \cup
                         {[type |-> "AppendEntriesResponse",
                           term |-> currentTerm'[s],
                           success |-> success,
                           matchIndex |-> IF success THEN m.prevLogIndex + Len(m.entries)
                                          ELSE 0,
                           from |-> s]}
          /\ UNCHANGED <<lastApplied, nextIndex, matchIndex, snapshotLastIndex,
                         snapshotLastTerm, configChangeInProgress, votingNodes>>

RecvAppendEntriesResponse(s, m) ==
    /\ m.type = "AppendEntriesResponse"
    /\ m.from # s
    /\ state[s] = "LEADER"
    /\ IF m.term > currentTerm[s]
       THEN BecomeFollower(s, m.term) /\ messages' = messages \ {m}
       ELSE /\ IF m.success
               THEN /\ matchIndex' = [matchIndex EXCEPT ![s][m.from] = m.matchIndex]
                    /\ nextIndex' = [nextIndex EXCEPT ![s][m.from] = m.matchIndex + 1]
               ELSE /\ nextIndex' = [nextIndex EXCEPT ![s][m.from] = 
                                     Max(1, nextIndex[s][m.from] - 1)]
                    /\ UNCHANGED matchIndex
            /\ messages' = messages \ {m}
            /\ UNCHANGED <<currentTerm, state, votedFor, log, commitIndex,
                           lastApplied, electionTimeout, heartbeatTimeout,
                           votesGranted, snapshotLastIndex, snapshotLastTerm,
                           configChangeInProgress, votingNodes>>

LogAppend(s, entry) ==
    /\ state[s] = "LEADER"
    /\ Len(log[s]) < MaxLogLen
    /\ entry.term = currentTerm[s]
    /\ log' = [log EXCEPT ![s] = Append(log[s], entry)]
    /\ UNCHANGED <<currentTerm, state, votedFor, commitIndex, lastApplied,
                   nextIndex, matchIndex, electionTimeout, heartbeatTimeout,
                   messages, votesGranted, snapshotLastIndex, snapshotLastTerm,
                   configChangeInProgress, votingNodes>>

LogCommit(s) ==
    /\ state[s] = "LEADER"
    /\ \E index \in (commitIndex[s] + 1)..LastLogIndex(s) :
        /\ GetLogTerm(s, index) = currentTerm[s]
        /\ IsQuorum({t \in Servers : matchIndex[s][t] >= index} \cup {s})
        /\ commitIndex' = [commitIndex EXCEPT ![s] = index]
    /\ UNCHANGED <<currentTerm, state, votedFor, log, lastApplied, nextIndex,
                   matchIndex, electionTimeout, heartbeatTimeout, messages,
                   votesGranted, snapshotLastIndex, snapshotLastTerm,
                   configChangeInProgress, votingNodes>>

LogApply(s) ==
    /\ lastApplied[s] < commitIndex[s]
    /\ lastApplied' = [lastApplied EXCEPT ![s] = lastApplied[s] + 1]
    /\ UNCHANGED <<currentTerm, state, votedFor, log, commitIndex, nextIndex,
                   matchIndex, electionTimeout, heartbeatTimeout, messages,
                   votesGranted, snapshotLastIndex, snapshotLastTerm,
                   configChangeInProgress, votingNodes>>

AddNode(s, newNode) ==
    /\ state[s] = "LEADER"
    /\ newNode \notin votingNodes
    /\ ~configChangeInProgress[s]
    /\ LET entry == [term |-> currentTerm[s], type |-> "ADD_NODE", data |-> ToString(newNode)]
       IN /\ log' = [log EXCEPT ![s] = Append(log[s], entry)]
          /\ configChangeInProgress' = [configChangeInProgress EXCEPT ![s] = TRUE]
    /\ UNCHANGED <<currentTerm, state, votedFor, commitIndex, lastApplied,
                   nextIndex, matchIndex, electionTimeout, heartbeatTimeout,
                   messages, votesGranted, snapshotLastIndex, snapshotLastTerm,
                   votingNodes>>

RemoveNode(s, oldNode) ==
    /\ state[s] = "LEADER"
    /\ oldNode \in votingNodes
    /\ oldNode # s
    /\ ~configChangeInProgress[s]
    /\ LET entry == [term |-> currentTerm[s], type |-> "REMOVE_NODE", data |-> ToString(oldNode)]
       IN /\ log' = [log EXCEPT ![s] = Append(log[s], entry)]
          /\ configChangeInProgress' = [configChangeInProgress EXCEPT ![s] = TRUE]
    /\ UNCHANGED <<currentTerm, state, votedFor, commitIndex, lastApplied,
                   nextIndex, matchIndex, electionTimeout, heartbeatTimeout,
                   messages, votesGranted, snapshotLastIndex, snapshotLastTerm,
                   votingNodes>>

ApplyConfigChange(s) ==
    /\ lastApplied[s] < commitIndex[s]
    /\ LET index == lastApplied[s] + 1
           entry == log[s][index - snapshotLastIndex[s]]
       IN /\ entry.type \in {"ADD_NODE", "REMOVE_NODE"}
          /\ IF entry.type = "ADD_NODE"
             THEN votingNodes' = votingNodes \cup {entry.data}
             ELSE votingNodes' = votingNodes \ {entry.data}
          /\ configChangeInProgress' = [configChangeInProgress EXCEPT ![s] = FALSE]
          /\ lastApplied' = [lastApplied EXCEPT ![s] = index]
    /\ UNCHANGED <<currentTerm, state, votedFor, log, commitIndex, nextIndex,
                   matchIndex, electionTimeout, heartbeatTimeout, messages,
                   votesGranted, snapshotLastIndex, snapshotLastTerm>>

SnapshotBegin(s) ==
    /\ lastApplied[s] > snapshotLastIndex[s]
    /\ snapshotLastIndex' = [snapshotLastIndex EXCEPT ![s] = lastApplied[s]]
    /\ snapshotLastTerm' = [snapshotLastTerm EXCEPT ![s] = 
                            GetLogTerm(s, lastApplied[s])]
    /\ UNCHANGED <<currentTerm, state, votedFor, log, commitIndex, lastApplied,
                   nextIndex, matchIndex, electionTimeout, heartbeatTimeout,
                   messages, votesGranted, configChangeInProgress, votingNodes>>

SnapshotEnd(s) ==
    /\ snapshotLastIndex[s] > 0
    /\ log' = [log EXCEPT ![s] = SubSeq(log[s], snapshotLastIndex[s] + 1, Len(log[s]))]
    /\ UNCHANGED <<currentTerm, state, votedFor, commitIndex, lastApplied,
                   nextIndex, matchIndex, electionTimeout, heartbeatTimeout,
                   messages, votesGranted, snapshotLastIndex, snapshotLastTerm,
                   configChangeInProgress, votingNodes>>

Next ==
    \/ \E s \in Servers : ElectionTimeout(s)
    \/ \E s \in Servers : HeartbeatTimeout(s)
    \/ \E s \in Servers : BecomePreCandidate(s)
    \/ \E s \in Servers : BecomeCandidate(s)
    \/ \E s \in Servers : BecomeLeader(s)
    \/ \E s \in Servers : SendHeartbeat(s)
    \/ \E s \in Servers, t \in Servers : SendAppendEntries(s, t)
    \/ \E s \in Servers, m \in messages : RecvRequestVote(s, m)
    \/ \E s \in Servers, m \in messages : RecvRequestVoteResponse(s, m)
    \/ \E s \in Servers, m \in messages : RecvAppendEntries(s, m)
    \/ \E s \in Servers, m \in messages : RecvAppendEntriesResponse(s, m)
    \/ \E s \in Servers, entry \in [term: 0..MaxTerm, type: STRING, data: STRING] :
        LogAppend(s, entry)
    \/ \E s \in Servers : LogCommit(s)
    \/ \E s \in Servers : LogApply(s)
    \/ \E s \in Servers, n \in Servers : AddNode(s, n)
    \/ \E s \in Servers, n \in Servers : RemoveNode(s, n)
    \/ \E s \in Servers : ApplyConfigChange(s)
    \/ \E s \in Servers : SnapshotBegin(s)
    \/ \E s \in Servers : SnapshotEnd(s)

Spec == Init /\ [][Next]_vars

====