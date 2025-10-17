---- MODULE etcdraft ----
EXTENDS Naturals, Sequences, FiniteSets, TLC
CONSTANTS Nodes, FaultyNodes, None
ASSUME Cardinality(Nodes) > 0

States == {"Follower", "Candidate", "Leader"}
MessageType == {"RequestVote", "RequestVoteResponse", "AppendEntries", "AppendEntriesResponse", "Propose", "ReadIndex", "Response"}
LogEntry == [term : Nat, cmd : ANY]

NodeState == [
    state: States, 
    currentTerm: Nat, 
    votedFor: Nodes \union {"None"}, 
    log: Seq(LogEntry), 
    commitIndex: Nat, 
    lastApplied: Nat,
    nextIndex: [Nodes -> Nat],
    matchIndex: [Nodes -> Nat],
    votesResponded: SUBSET Nodes,
    votesGranted: SUBSET Nodes,
    smState: Seq(ANY)
]

InitNodeState == [
    state |-> "Follower",
    currentTerm |-> 0,
    votedFor |-> "None",
    log |-> << >>,
    commitIndex |-> 0,
    lastApplied |-> 0,
    nextIndex |-> [n \in Nodes |-> 1],
    matchIndex |-> [n \in Nodes |-> 0],
    votesResponded |-> {},
    votesGranted |-> {},
    smState |-> << >>
]

RequestVoteMsg == [type : {"RequestVote"}, term : Nat, candidateId : Nodes, lastLogIndex : Nat, lastLogTerm : Nat, to: Nodes]
RequestVoteResponseMsg == [type : {"RequestVoteResponse"}, term : Nat, voteGranted : BOOLEAN, from: Nodes, to: Nodes]
AppendEntriesMsg == [type : {"AppendEntries"}, term : Nat, leaderId : Nodes, prevLogIndex : Nat, prevLogTerm : Nat, entries: Seq(LogEntry), leaderCommit : Nat, to: Nodes]
AppendEntriesResponseMsg == [type : {"AppendEntriesResponse"}, term : Nat, success : BOOLEAN, matchIndex: Nat, from: Nodes, to: Nodes]
ProposeMsg == [type : {"Propose"}, cmd : ANY, to: Nodes]
ReadIndexMsg == [type : {"ReadIndex"}, to: Nodes]
ResponseMsg == [type : {"Response"}, result : ANY, from: Nodes]

Message == RequestVoteMsg \union RequestVoteResponseMsg \union AppendEntriesMsg \union AppendEntriesResponseMsg \union ProposeMsg \union ReadIndexMsg \union ResponseMsg

VARIABLES nodeState, messages

Init == 
    /\ nodeState = [n \in Nodes |-> InitNodeState]
    /\ messages = {}

Quorum == Cardinality(Nodes) \div 2 + 1

IsUpToDate(logIndex, logTerm, lastLogIndex, lastLogTerm) ==
    \/ logTerm > lastLogTerm
    \/ (logTerm = lastLogTerm /\ logIndex >= lastLogIndex)

HandleRequestVote(n, msg) ==
    LET state == nodeState[n]
    IN
    IF msg.term < state.currentTerm THEN
        /\ messages' = messages \union {[type |-> "RequestVoteResponse", term |-> state.currentTerm, voteGranted |-> FALSE, from |-> n, to |-> msg.candidateId]}
        /\ nodeState' = nodeState
    ELSE
        LET newState == IF msg.term > state.currentTerm THEN [state EXCEPT !.state = "Follower", !.currentTerm = msg.term, !.votedFor = "None"] ELSE state
        IN
        LET lastLogIndex == Len(newState.log)
            lastLogTerm == IF lastLogIndex > 0 THEN newState.log[lastLogIndex].term ELSE 0
            grant == 
                /\ (newState.votedFor = "None" \/ newState.votedFor = msg.candidateId)
                /\ IsUpToDate(msg.lastLogIndex, msg.lastLogTerm, lastLogIndex, lastLogTerm)
        IN
        /\ nodeState' = [nodeState EXCEPT ![n] = IF grant THEN [newState EXCEPT !.votedFor = msg.candidateId] ELSE newState]
        /\ messages' = messages \union {[type |-> "RequestVoteResponse", term |-> msg.term, voteGranted |-> grant, from |-> n, to |-> msg.candidateId]}

HandleRequestVoteResponse(n, msg) ==
    LET state == nodeState[n]
    IN
    IF state.state = "Candidate" /\ state.currentTerm = msg.term THEN
        LET newVotesResponded == state.votesResponded \union {msg.from}
            newVotesGranted == IF msg.voteGranted THEN state.votesGranted \union {msg.from} ELSE state.votesGranted
            won == Cardinality(newVotesGranted) >= Quorum
            newState == [state EXCEPT !.votesResponded = newVotesResponded, !.votesGranted = newVotesGranted]
            updatedState == IF won THEN [newState EXCEPT !.state = "Leader"] ELSE newState
        IN
        /\ nodeState' = [nodeState EXCEPT ![n] = updatedState]
        /\ messages' = 
            IF won 
            THEN messages \union {[type |-> "AppendEntries", term |-> state.currentTerm, leaderId |-> n, 
                prevLogIndex |-> Len(state.log), prevLogTerm |-> IF Len(state.log) > 0 THEN state.log[Len(state.log)].term ELSE 0,
                entries |-> << >>, leaderCommit |-> state.commitIndex, to |-> m] : m \in Nodes \ {n}}
            ELSE messages
    ELSE
        /\ UNCHANGED <<nodeState, messages>>

LogMatch(log, prevIndex, prevTerm) ==
    prevIndex = 0 \/ (prevIndex <= Len(log) /\ log[prevIndex].term = prevTerm)

HandleAppendEntries(n, msg) ==
    LET state == nodeState[n]
    IN
    IF msg.term < state.currentTerm THEN
        /\ messages' = messages \union {[type |-> "AppendEntriesResponse", term |-> state.currentTerm, success |-> FALSE, matchIndex |-> 0, from |-> n, to |-> msg.leaderId]}
        /\ nodeState' = nodeState
    ELSE
        LET newState == 
            IF msg.term > state.currentTerm \/ state.state = "Candidate" THEN 
                [state EXCEPT !.state = "Follower", !.currentTerm = msg.term, !.votedFor = "None"] 
            ELSE state
        IN
        IF LogMatch(newState.log, msg.prevLogIndex, msg.prevLogTerm) THEN
            LET newLog == 
                IF \/ Len(msg.entries) = 0 
                   \/ (Len(newState.log) >= msg.prevLogIndex + 1 /\ newState.log[msg.prevLogIndex+1].term = msg.entries[1].term) 
                THEN newState.log 
                ELSE SubSeq(newState.log, 1, msg.prevLogIndex) \o msg.entries
            IN
            LET newCommitIndex == Min(msg.leaderCommit, msg.prevLogIndex + Len(msg.entries))
            IN
            /\ nodeState' = [nodeState EXCEPT ![n] = 
                [newState EXCEPT !.log = newLog, !.commitIndex = newCommitIndex, !.currentTerm = msg.term]]
            /\ messages' = messages \union {[type |-> "AppendEntriesResponse", term |-> msg.term, success |-> TRUE, matchIndex |-> msg.prevLogIndex + Len(msg.entries), from |-> n, to |-> msg.leaderId]}
        ELSE
            /\ nodeState' = [nodeState EXCEPT ![n] = [newState EXCEPT !.currentTerm = msg.term]]
            /\ messages' = messages \union {[type |-> "AppendEntriesResponse", term |-> msg.term, success |-> FALSE, matchIndex |-> 0, from |-> n, to |-> msg.leaderId]}

HandleAppendEntriesResponse(n, msg) ==
    LET state == nodeState[n]
    IN
    IF state.state = "Leader" /\ state.currentTerm = msg.term THEN
        LET pr == msg.from
        IN
        IF msg.success THEN
            LET newNextIndex == msg.matchIndex + 1
                newMatchIndex == msg.matchIndex
                newNextIndexMap == [state.nextIndex EXCEPT ![pr] = newNextIndex]
                newMatchIndexMap == [state.matchIndex EXCEPT ![pr] = newMatchIndex]
                N == Max({ m \in 1..Len(state.log) : 
                           state.log[m].term = state.currentTerm /\
                           Cardinality({p \in Nodes : state.matchIndex[p] >= m}) >= Quorum })
                newCommitIndex == IF N > state.commitIndex THEN N ELSE state.commitIndex
            IN
            /\ nodeState' = [nodeState EXCEPT ![n] = 
                [state EXCEPT !.nextIndex = newNextIndexMap, 
                          !.matchIndex = newMatchIndexMap,
                          !.commitIndex = newCommitIndex]]
            /\ messages' = messages
        ELSE
            /\ nodeState' = [nodeState EXCEPT ![n] = [state EXCEPT !.nextIndex[pr] = state.nextIndex[pr] - 1]]
            /\ messages' = messages \union {[type |-> "AppendEntries", term |-> state.currentTerm, leaderId |-> n, 
                prevLogIndex |-> state.nextIndex[pr] - 1, 
                prevLogTerm |-> IF state.nextIndex[pr] - 1 > 0 THEN state.log[state.nextIndex[pr] - 1].term ELSE 0,
                entries |-> SubSeq(state.log, state.nextIndex[pr], Len(state.log)), 
                leaderCommit |-> state.commitIndex, to |-> pr]}
    ELSE
        /\ UNCHANGED <<nodeState, messages>>

ApplyLog(n) ==
    LET state == nodeState[n]
    IN
    IF state.commitIndex > state.lastApplied THEN
        LET entry == state.log[state.lastApplied + 1]
            newSMState == state.smState \o <<entry.cmd>>
        IN
        /\ nodeState' = [nodeState EXCEPT ![n] = 
            [state EXCEPT !.lastApplied = state.lastApplied + 1, !.smState = newSMState]]
        /\ messages' = messages
    ELSE
        /\ UNCHANGED <<nodeState, messages>>

LeaderAppend(n, cmd) ==
    LET state == nodeState[n]
    IN
    IF state.state = "Leader" THEN
        LET newEntry == [term |-> state.currentTerm, cmd |-> cmd]
            newLog == state.log \o <<newEntry>>
        IN
        /\ nodeState' = [nodeState EXCEPT ![n] = [state EXCEPT !.log = newLog]]
        /\ messages' = messages \union {[type |-> "AppendEntries", term |-> state.currentTerm, leaderId |-> n, 
            prevLogIndex |-> Len(state.log), 
            prevLogTerm |-> IF Len(state.log) > 0 THEN state.log[Len(state.log)].term ELSE 0,
            entries |-> <<newEntry>>, leaderCommit |-> state.commitIndex, to |-> m] : m \in Nodes \ {n}}
    ELSE
        /\ UNCHANGED <<nodeState, messages>>

HandleReadIndex(n, msg) ==
    LET state == nodeState[n]
    IN
    IF state.state = "Leader" THEN
        /\ messages' = messages \union {[type |-> "AppendEntries", term |-> state.currentTerm, leaderId |-> n, 
            prevLogIndex |-> Len(state.log), 
            prevLogTerm |-> IF Len(state.log) > 0 THEN state.log[Len(state.log)].term ELSE 0,
            entries |-> << >>, leaderCommit |-> state.commitIndex, to |-> m] : m \in Nodes \ {n}}
        /\ UNCHANGED <<nodeState>>
    ELSE
        /\ UNCHANGED <<nodeState, messages>>

NodeCrash(n) ==
    /\ nodeState' = [nodeState EXCEPT ![n] = [state |-> "Follower", currentTerm |-> 0, votedFor |-> "None", log |-> << >>, 
        commitIndex |-> 0, lastApplied |-> 0, nextIndex |-> [m \in Nodes |-> 1], matchIndex |-> [m \in Nodes |-> 0], 
        votesResponded |-> {}, votesGranted |-> {}, smState |-> << >>]]
    /\ messages' = {msg \in messages: msg.to /= n /\ msg.from /= n}

DropMessage(msg) ==
    /\ messages' = messages \ {msg}
    /\ UNCHANGED <<nodeState>>

Next == 
    \/ \E n \in Nodes: 
        LET state == nodeState[n]
        IN
        /\ state.state \in {"Follower", "Candidate"}
        /\ \E newTerm \in Nat: newTerm > state.currentTerm
        /\ nodeState' = [nodeState EXCEPT ![n] = 
            [state EXCEPT !.state = "Candidate", !.currentTerm = newTerm, !.votedFor = n, !.votesResponded = {n}, !.votesGranted = {n}]]
        /\ messages' = messages \union {[type |-> "RequestVote", term |-> newTerm, candidateId |-> n, 
            lastLogIndex |-> Len(state.log), lastLogTerm |-> IF Len(state.log) > 0 THEN state.log[Len(state.log)].term ELSE 0, 
            to |-> m] : m \in Nodes \ {n}}
    \/ \E msg \in messages, n \in Nodes: 
        /\ n = msg.to
        /\ \/ (msg.type = "RequestVote") /\ HandleRequestVote(n, msg)
           \/ (msg.type = "RequestVoteResponse") /\ HandleRequestVoteResponse(n, msg)
           \/ (msg.type = "AppendEntries") /\ HandleAppendEntries(n, msg)
           \/ (msg.type = "AppendEntriesResponse") /\ HandleAppendEntriesResponse(n, msg)
           \/ (msg.type = "Propose") /\ LeaderAppend(n, msg.cmd)
           \/ (msg.type = "ReadIndex") /\ HandleReadIndex(n, msg)
    \/ \E n \in Nodes: ApplyLog(n)
    \/ \E n \in FaultyNodes: NodeCrash(n)
    \/ \E msg \in messages: DropMessage(msg)

TypeInvariant == 
    \A n \in Nodes:
        /\ nodeState[n].currentTerm \in Nat
        /\ nodeState[n].votedFor \in (Nodes \union {"None"})
        /\ nodeState[n].commitIndex <= Len(nodeState[n].log)
        /\ nodeState[n].lastApplied <= nodeState[n].commitIndex
        /\ nodeState[n].lastApplied <= Len(nodeState[n].smState)
        /\ \A m \in Nodes: nodeState[n].nextIndex[m] <= Len(nodeState[n].log) + 1

ElectionSafety == 
    \A n1, n2 \in Nodes: 
        (nodeState[n1].state = "Leader" /\ nodeState[n2].state = "Leader" /\ n1 /= n2) => 
            nodeState[n1].currentTerm /= nodeState[n2].currentTerm

LeaderAppendOnly == 
    \A n \in Nodes, t1, t2 \in DOMAIN nodeState:
        t1 < t2 => \/ Len(nodeState[n].log)@t1 < Len(nodeState[n].log)@t2
                   \/ \E i \in 1..Min(Len(nodeState[n].log)@t1, Len(nodeState[n].log)@t2):
                         nodeState[n].log@t1[i] /= nodeState[n].log@t2[i]

LogMatching == 
    \A n1, n2 \in Nodes, i \in 1..Min(Len(nodeState[n1].log), Len(nodeState[n2].log)):
        (nodeState[n1].log[i].term = nodeState[n2].log[i].term) => 
            nodeState[n1].log[i].cmd = nodeState[n2].log[i].cmd

LeaderCompleteness == 
    \A term \in Nat, n \in Nodes:
        (nodeState[n].commitIndex > 0 /\ nodeState[n].log[nodeState[n].commitIndex].term = term) =>
            \A leader \in Nodes: 
                (nodeState[leader].state = "Leader" /\ nodeState[leader].currentTerm > term) => 
                    \E i \in 1..Len(nodeState[leader].log): 
                        nodeState[leader].log[i] = nodeState[n].log[nodeState[n].commitIndex]

StateMachineSafety == 
    \A n1, n2 \in Nodes, i \in 1..Min(Len(nodeState[n1].smState), Len(nodeState[n2].smState)):
        nodeState[n1].smState[i] = nodeState[n2].smState[i]

Invariants == 
    /\ TypeInvariant
    /\ ElectionSafety
    /\ LeaderAppendOnly
    /\ LogMatching
    /\ LeaderCompleteness
    /\ StateMachineSafety

====