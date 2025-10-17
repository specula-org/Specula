---- MODULE etcdraft ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS
    Servers,
    Commands,
    Nil,
    DefaultValue,
    ElectionTimeout,
    HeartbeatTimeout

ASSUME
    /\ Servers = { "s1", "s2", "s3" }
    /\ Commands = { [op |-> "Put", key |-> "k1", val |-> "v1"], [op |-> "Get", key |-> "k1"] }
    /\ Nil \notin Servers
    /\ IsFiniteSet(Servers)

VARIABLES
    state,
    currentTerm,
    votedFor,
    log,
    commitIndex,
    appliedIndex,
    nextIndex,
    matchIndex,
    leader,
    votesGranted,
    messages,
    kvStore,
    clientRequests,
    clientResponses,
    electionTimer,
    leaderTransferTarget

vars == << state, currentTerm, votedFor, log, commitIndex, appliedIndex,
           nextIndex, matchIndex, leader, votesGranted, messages,
           kvStore, clientRequests, clientResponses, electionTimer,
           leaderTransferTarget >>

QuorumSize == (Cardinality(Servers) \div 2) + 1

LastEntry(l) == IF Len(l) = 0 THEN [term |-> 0, index |-> 0] ELSE l[Len(l)]
LastTerm(l) == LastEntry(l).term
LastIndex(l) == LastEntry(l).index

IsUpToDate(logA, logB) ==
    LET lastTermA == LastTerm(logA)
        lastIndexA == LastIndex(logA)
        lastTermB == LastTerm(logB)
        lastIndexB == LastIndex(logB)
    IN \/ lastTermA > lastTermB
       \/ (lastTermA = lastTermB) /\ (lastIndexA >= lastIndexB)

TypeOK ==
    /\ state \in [Servers -> {"Follower", "Candidate", "PreCandidate", "Leader"}]
    /\ currentTerm \in [Servers -> Nat]
    /\ votedFor \in [Servers -> Servers \cup {Nil}]
    /\ \A i \in Servers: IsSequence(log[i])
    /\ commitIndex \in [Servers -> Nat]
    /\ appliedIndex \in [Servers -> Nat]
    /\ nextIndex \in [Servers -> [Servers -> Nat]]
    /\ matchIndex \in [Servers -> [Servers -> Nat]]
    /\ leader \in Servers \cup {Nil}
    /\ votesGranted \in [Servers -> SUBSET Servers]
    /\ \A msg \in messages:
        /\ msg.type \in {"AppendEntriesRequest", "AppendEntriesResponse",
                         "RequestVoteRequest", "RequestVoteResponse",
                         "PreVoteRequest", "PreVoteResponse"}
        /\ msg.from \in Servers
        /\ msg.to \in Servers
        /\ msg.mTerm \in Nat
    /\ leaderTransferTarget \in [Servers -> Servers \cup {Nil}]

Init ==
    /\ state = [i \in Servers |-> "Follower"]
    /\ currentTerm = [i \in Servers |-> 0]
    /\ votedFor = [i \in Servers |-> Nil]
    /\ log = [i \in Servers |-> <<>>]
    /\ commitIndex = [i \in Servers |-> 0]
    /\ appliedIndex = [i \in Servers |-> 0]
    /\ nextIndex = [i \in Servers |-> [j \in Servers |-> 1]]
    /\ matchIndex = [i \in Servers |-> [j \in Servers |-> 0]]
    /\ leader = Nil
    /\ votesGranted = [i \in Servers |-> {}]
    /\ messages = {}
    /\ kvStore = [i \in Servers |-> [k \in {} |-> DefaultValue]]
    /\ clientRequests = {}
    /\ clientResponses = {}
    /\ electionTimer = [i \in Servers |-> 0]
    /\ leaderTransferTarget = [i \in Servers |-> Nil]

ClientRequest(cmd) ==
    /\ clientRequests' = clientRequests \cup {cmd}
    /\ UNCHANGED << vars \ {clientRequests} >>

BecomeFollower(i, term) ==
    /\ state' = [state EXCEPT ![i] = "Follower"]
    /\ currentTerm' = [currentTerm EXCEPT ![i] = term]
    /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
    /\ leader' = IF state[i] = "Leader" THEN Nil ELSE leader
    /\ electionTimer' = [electionTimer EXCEPT ![i] = 0]
    /\ leaderTransferTarget' = [leaderTransferTarget EXCEPT ![i] = Nil]

ElectionTimeout(i) ==
    /\ state[i] \in {"Follower", "Candidate", "PreCandidate"}
    /\ electionTimer[i] >= ElectionTimeout
    /\ state' = [state EXCEPT ![i] = "PreCandidate"]
    /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i]]
    /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
    /\ votesGranted' = [votesGranted EXCEPT ![i] = {i}]
    /\ electionTimer' = [electionTimer EXCEPT ![i] = 0]
    /\ messages' = messages \cup
        {[ type |-> "PreVoteRequest", from |-> i, to |-> j,
           mTerm |-> currentTerm[i] + 1,
           lastLogIndex |-> LastIndex(log[i]),
           lastLogTerm |-> LastTerm(log[i]) ] : j \in Servers}
    /\ UNCHANGED << log, commitIndex, appliedIndex, nextIndex, matchIndex, leader,
                    kvStore, clientRequests, clientResponses, leaderTransferTarget >>

HandlePreVoteRequest(i, msg) ==
    LET myLastLogTerm = LastTerm(log[i])
        myLastLogIndex = LastIndex(log[i])
        candidateIsUpToDate = IsUpToDate([ [term |-> msg.lastLogTerm, index |-> msg.lastLogIndex] ], log[i])
    IN
    /\ msg.mTerm > currentTerm[i]
    /\ candidateIsUpToDate
    /\ messages' = messages \ {msg} \cup
        { [ type |-> "PreVoteResponse", from |-> i, to |-> msg.from,
            mTerm |-> msg.mTerm, granted |-> TRUE ] }
    /\ UNCHANGED << vars \ {messages} >>

HandlePreVoteResponse(i, msg) ==
    /\ state[i] = "PreCandidate"
    /\ msg.mTerm = currentTerm[i] + 1
    /\ LET newVotes = IF msg.granted THEN votesGranted[i] \cup {msg.from} ELSE votesGranted[i]
       IN
       /\ votesGranted' = [votesGranted EXCEPT ![i] = newVotes]
       /\ IF Cardinality(newVotes) >= QuorumSize THEN
            /\ state' = [state EXCEPT ![i] = "Candidate"]
            /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
            /\ votedFor' = [votedFor EXCEPT ![i] = i]
            /\ votesGranted' = [votesGranted EXCEPT ![i] = {i}]
            /\ electionTimer' = [electionTimer EXCEPT ![i] = 0]
            /\ messages' = (messages \ {msg}) \cup
                {[ type |-> "RequestVoteRequest", from |-> i, to |-> j,
                   mTerm |-> currentTerm[i] + 1,
                   lastLogIndex |-> LastIndex(log[i]),
                   lastLogTerm |-> LastTerm(log[i]) ] : j \in Servers}
       ELSE
            /\ messages' = messages \ {msg}
            /\ UNCHANGED << state, currentTerm, votedFor, electionTimer >>
    /\ UNCHANGED << log, commitIndex, appliedIndex, nextIndex, matchIndex, leader,
                    kvStore, clientRequests, clientResponses, leaderTransferTarget >>

HandleRequestVoteRequest(i, msg) ==
    LET myLastLogTerm = LastTerm(log[i])
        myLastLogIndex = LastIndex(log[i])
        candidateIsUpToDate = IsUpToDate([ [term |-> msg.lastLogTerm, index |-> msg.lastLogIndex] ], log[i])
        grantVote = /\ msg.mTerm = currentTerm[i]
                    /\ (votedFor[i] = Nil \/ votedFor[i] = msg.from)
                    /\ candidateIsUpToDate
    IN
    /\ messages' = messages \ {msg} \cup
        { [ type |-> "RequestVoteResponse", from |-> i, to |-> msg.from,
            mTerm |-> currentTerm[i], granted |-> grantVote ] }
    /\ IF grantVote THEN
        /\ votedFor' = [votedFor EXCEPT ![i] = msg.from]
        /\ electionTimer' = [electionTimer EXCEPT ![i] = 0]
    ELSE
        /\ UNCHANGED << votedFor, electionTimer >>
    /\ UNCHANGED << state, currentTerm, log, commitIndex, appliedIndex, nextIndex,
                    matchIndex, leader, votesGranted, kvStore, clientRequests,
                    clientResponses, leaderTransferTarget >>

HandleRequestVoteResponse(i, msg) ==
    /\ state[i] = "Candidate"
    /\ msg.mTerm = currentTerm[i]
    /\ LET newVotes = IF msg.granted THEN votesGranted[i] \cup {msg.from} ELSE votesGranted[i]
       IN
       /\ votesGranted' = [votesGranted EXCEPT ![i] = newVotes]
       /\ IF Cardinality(newVotes) >= QuorumSize THEN
            /\ state' = [state EXCEPT ![i] = "Leader"]
            /\ leader' = i
            /\ nextIndex' = [nextIndex EXCEPT ![i] = [j \in Servers |-> LastIndex(log[i]) + 1]]
            /\ matchIndex' = [matchIndex EXCEPT ![i] = [j \in Servers |-> 0]]
            /\ messages' = (messages \ {msg}) \cup
                {[ type |-> "AppendEntriesRequest", from |-> i, to |-> j,
                   mTerm |-> currentTerm[i], prevLogIndex |-> LastIndex(log[i]),
                   prevLogTerm |-> LastTerm(log[i]), entries |-> <<>>,
                   leaderCommit |-> commitIndex[i] ] : j \in Servers \ {i}}
       ELSE
            /\ messages' = messages \ {msg}
            /\ UNCHANGED << state, leader, nextIndex, matchIndex >>
    /\ UNCHANGED << currentTerm, votedFor, log, commitIndex, appliedIndex, electionTimer,
                    kvStore, clientRequests, clientResponses, leaderTransferTarget >>

HandleClientProposal(i) ==
    /\ state[i] = "Leader"
    /\ leaderTransferTarget[i] = Nil
    /\ \E cmd \in clientRequests:
        LET newEntry = [term |-> currentTerm[i], index |-> LastIndex(log[i]) + 1, command |-> cmd]
            newLog = Append(log[i], newEntry)
        IN
        /\ log' = [log EXCEPT ![i] = newLog]
        /\ clientRequests' = clientRequests \ {cmd}
        /\ UNCHANGED << vars \ {log, clientRequests} >>

Heartbeat(i) ==
    /\ state[i] = "Leader"
    /\ \E j \in Servers \ {i}:
        /\ messages' = messages \cup
            {[ type |-> "AppendEntriesRequest", from |-> i, to |-> j,
               mTerm |-> currentTerm[i],
               prevLogIndex |-> LastIndex(log[i]),
               prevLogTerm |-> LastTerm(log[i]),
               entries |-> <<>>,
               leaderCommit |-> commitIndex[i] ]}
        /\ UNCHANGED << vars \ {messages} >>

SendAppendEntries(i) ==
    /\ state[i] = "Leader"
    /\ \E j \in Servers \ {i}:
        LET ni = nextIndex[i][j]
        IN
        /\ ni <= LastIndex(log[i]) + 1
        /\ LET prevLogIndex = ni - 1
              prevLogTerm = IF prevLogIndex > 0 THEN log[i][prevLogIndex].term ELSE 0
              entriesToSend = SubSeq(log[i], ni, LastIndex(log[i]))
           IN
           /\ messages' = messages \cup
               {[ type |-> "AppendEntriesRequest", from |-> i, to |-> j,
                  mTerm |-> currentTerm[i], prevLogIndex |-> prevLogIndex,
                  prevLogTerm |-> prevLogTerm, entries |-> entriesToSend,
                  leaderCommit |-> commitIndex[i] ]}
           /\ UNCHANGED << vars \ {messages} >>

HandleAppendEntriesRequest(i, msg) ==
    /\ msg.mTerm >= currentTerm[i]
    /\ LET newTerm = IF msg.mTerm > currentTerm[i] THEN msg.mTerm ELSE currentTerm[i]
        newVotedFor = IF msg.mTerm > currentTerm[i] THEN Nil ELSE votedFor[i]
    IN
    /\ currentTerm' = [currentTerm EXCEPT ![i] = newTerm]
    /\ votedFor' = [votedFor EXCEPT ![i] = newVotedFor]
    /\ state' = [state EXCEPT ![i] = "Follower"]
    /\ leader' = msg.from
    /\ electionTimer' = [electionTimer EXCEPT ![i] = 0]
    /\ LET logOK = \/ msg.prevLogIndex = 0
                   \/ ( /\ msg.prevLogIndex <= LastIndex(log[i])
                        /\ log[i][msg.prevLogIndex].term = msg.prevLogTerm )
       IN
       /\ IF logOK THEN
            LET newEntries = msg.entries
                firstNewIndex = msg.prevLogIndex + 1
                existingEntries = SubSeq(log[i], 1, msg.prevLogIndex)
                finalLog = existingEntries \o newEntries
            IN
            /\ log' = [log EXCEPT ![i] = finalLog]
            /\ commitIndex' = [commitIndex EXCEPT ![i] = min(msg.leaderCommit, LastIndex(finalLog))]
            /\ messages' = messages \ {msg} \cup
                {[ type |-> "AppendEntriesResponse", from |-> i, to |-> msg.from,
                   mTerm |-> newTerm, success |-> TRUE,
                   matchIndex |-> LastIndex(finalLog) ]}
       ELSE
            /\ messages' = messages \ {msg} \cup
                {[ type |-> "AppendEntriesResponse", from |-> i, to |-> msg.from,
                   mTerm |-> newTerm, success |-> FALSE,
                   matchIndex |-> 0 ]}
            /\ UNCHANGED << log, commitIndex >>
    /\ UNCHANGED << appliedIndex, nextIndex, matchIndex, votesGranted, kvStore,
                    clientRequests, clientResponses, leaderTransferTarget >>

HandleAppendEntriesResponse(i, msg) ==
    /\ state[i] = "Leader"
    /\ msg.mTerm = currentTerm[i]
    /\ IF msg.success THEN
        /\ nextIndex' = [nextIndex EXCEPT ![i][msg.from] = msg.matchIndex + 1]
        /\ matchIndex' = [matchIndex EXCEPT ![i][msg.from] = msg.matchIndex]
    ELSE
        /\ nextIndex' = [nextIndex EXCEPT ![i][msg.from] = nextIndex[i][msg.from] - 1]
        /\ UNCHANGED << matchIndex >>
    /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, appliedIndex,
                    leader, votesGranted, messages, kvStore, clientRequests,
                    clientResponses, electionTimer, leaderTransferTarget >>

AdvanceCommitIndex(i) ==
    /\ state[i] = "Leader"
    /\ LET newCommitIndex =
        Max({ N \in (commitIndex[i]+1)..LastIndex(log[i]) |
              /\ log[i][N].term = currentTerm[i]
              /\ Cardinality({j \in Servers | matchIndex[i][j] >= N}) >= QuorumSize })
    IN
    /\ commitIndex' = [commitIndex EXCEPT ![i] = newCommitIndex]
    /\ UNCHANGED << vars \ {commitIndex} >>

ApplyCommitted(i) ==
    /\ commitIndex[i] > appliedIndex[i]
    /\ LET newAppliedIndex = appliedIndex[i] + 1
           entry = log[i][newAppliedIndex]
           cmd = entry.command
       IN
       /\ appliedIndex' = [appliedIndex EXCEPT ![i] = newAppliedIndex]
       /\ IF cmd.op = "Put" THEN
            /\ kvStore' = [kvStore EXCEPT ![i][cmd.key] = cmd.val]
            /\ clientResponses' = clientResponses \cup {[op |-> "Put", key |-> cmd.key, success |-> TRUE]}
       ELSE
            /\ UNCHANGED << kvStore, clientResponses >>
    /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, nextIndex,
                    matchIndex, leader, votesGranted, messages, clientRequests,
                    electionTimer, leaderTransferTarget >>

ReceiveMessage(i) ==
    \E msg \in messages:
    /\ msg.to = i
    /\ IF msg.mTerm > currentTerm[i] THEN
        /\ LET newTerm = msg.mTerm
           IN
           /\ BecomeFollower(i, newTerm)
           /\ messages' = messages \ {msg}
           /\ UNCHANGED << log, commitIndex, appliedIndex, nextIndex, matchIndex,
                           votesGranted, kvStore, clientRequests, clientResponses >>
    /\ ELSE IF msg.mTerm < currentTerm[i] THEN
        /\ messages' = messages \ {msg}
        /\ UNCHANGED << vars \ {messages} >>
    /\ ELSE
        /\ CASE msg.type = "PreVoteRequest" -> HandlePreVoteRequest(i, msg)
        []     msg.type = "PreVoteResponse" -> HandlePreVoteResponse(i, msg)
        []     msg.type = "RequestVoteRequest" -> HandleRequestVoteRequest(i, msg)
        []     msg.type = "RequestVoteResponse" -> HandleRequestVoteResponse(i, msg)
        []     msg.type = "AppendEntriesRequest" -> HandleAppendEntriesRequest(i, msg)
        []     msg.type = "AppendEntriesResponse" -> HandleAppendEntriesResponse(i, msg)

Tick(i) ==
    /\ electionTimer' = [electionTimer EXCEPT ![i] = electionTimer[i] + 1]
    /\ UNCHANGED << vars \ {electionTimer} >>

Crash(i) ==
    /\ state' = [state EXCEPT ![i] = "Crashed"]
    /\ UNCHANGED << vars \ {state} >>

Restart(i) ==
    /\ state[i] = "Crashed"
    /\ state' = [state EXCEPT ![i] = "Follower"]
    /\ electionTimer' = [electionTimer EXCEPT ![i] = 0]
    /\ UNCHANGED << currentTerm, votedFor, log, commitIndex, appliedIndex,
                    nextIndex, matchIndex, leader, votesGranted, messages,
                    kvStore, clientRequests, clientResponses, leaderTransferTarget >>

Next ==
    \/ \E cmd \in Commands : ClientRequest(cmd)
    \/ \E i \in Servers :
        \/ ElectionTimeout(i)
        \/ HandleClientProposal(i)
        \/ Heartbeat(i)
        \/ SendAppendEntries(i)
        \/ AdvanceCommitIndex(i)
        \/ ApplyCommitted(i)
        \/ ReceiveMessage(i)
        \/ Tick(i)
        \/ Crash(i)
        \/ Restart(i)

Spec == Init /\ [][Next]_vars

LeaderSafety ==
    \A t \in Nat:
        LET LeadersInTerm = {i \in Servers | state[i] = "Leader" /\ currentTerm[i] = t}
        IN Cardinality(LeadersInTerm) <= 1

TermMonotonicity ==
    \A i \in Servers:
        [][currentTerm[i] <= currentTerm'[i]]_vars

LogMatching ==
    \A i, j \in Servers:
        \A n \in 1..min(Len(log[i]), Len(log[j])):
            (log[i][n].term = log[j][n].term) => (log[i][n] = log[j][n])

LeaderCompleteness ==
    \A t \in Nat, idx \in Nat:
        ( \E i \in Servers:
            /\ idx <= commitIndex[i]
            /\ log[i][idx].term = t
        ) => (
            \A t2 \in (t+1)..(Max({currentTerm[s] : s \in Servers}) \cup {0}) :
                \A leader_j \in {j \in Servers | state[j] = "Leader" /\ currentTerm[j] = t2}:
                    idx <= LastIndex(log[leader_j])
        )

CommitSafety ==
    \A i, j \in Servers:
        commitIndex[i] <= LastIndex(log[i]) /\
        (commitIndex[i] > commitIndex[j] => log[i][commitIndex[j]+1].term >= currentTerm[j])

StateMachineSafety ==
    \A i, j \in Servers:
        \A idx \in 1..min(appliedIndex[i], appliedIndex[j]):
            log[i][idx] = log[j][idx]

EventuallyLeaderElected ==
    <>(\E i \in Servers: state[i] = "Leader")

EventuallyCommittedApplied ==
    \A i \in Servers:
        (commitIndex[i] > appliedIndex[i]) ~> (appliedIndex'[i] > appliedIndex[i])

====