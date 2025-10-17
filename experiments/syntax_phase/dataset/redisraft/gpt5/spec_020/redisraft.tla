---- MODULE redisraft ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS
    NODE,
    InitNodeSet,
    InitVotingSet,
    ELECTION_BASE,
    REQUEST_TIMEOUT,
    SNAPSHOT_THRESHOLD

ASSUME InitVotingSet \subseteq InitNodeSet
ASSUME InitNodeSet \subseteq NODE
ASSUME ELECTION_BASE \in Nat \ {0}
ASSUME REQUEST_TIMEOUT \in Nat \ {0}
ASSUME SNAPSHOT_THRESHOLD \in Nat

Nil == "Nil"
FOLLOWER == "FOLLOWER"
PRECANDIDATE == "PRECANDIDATE"
CANDIDATE == "CANDIDATE"
LEADER == "LEADER"
STATES == {FOLLOWER, PRECANDIDATE, CANDIDATE, LEADER}

NOOP == "NOOP"
NORMAL == "NORMAL"
ADD_NODE == "ADD_NODE"
ADD_NONVOTING_NODE == "ADD_NONVOTING_NODE"
REMOVE_NODE == "REMOVE_NODE"
ENTRYTYPE == {NOOP, NORMAL, ADD_NODE, ADD_NONVOTING_NODE, REMOVE_NODE}

ReqVote == "RequestVote"
ReqVoteResp == "RequestVoteResponse"
AppEnt == "AppendEntries"
AppEntResp == "AppendEntriesResponse"
SnapReq == "SnapshotRequest"
SnapResp == "SnapshotResponse"
MsgType == {ReqVote, ReqVoteResp, AppEnt, AppEntResp, SnapReq, SnapResp}

TimeoutRange == ELECTION_BASE..(2 * ELECTION_BASE)

ENTRY == [term: Nat, type: ENTRYTYPE, node: NODE \cup {Nil}]

min(a, b) == IF a <= b THEN a ELSE b
max(a, b) == IF a >= b THEN a ELSE b

VARIABLES
    NodeSet,
    VotingSet,
    state,               \* [NODE -> STATES]
    currentTerm,         \* [NODE -> Nat]
    votedFor,            \* [NODE -> NODE \cup {Nil}]
    leaderRef,           \* [NODE -> NODE \cup {Nil}]
    log,                 \* [NODE -> Seq(ENTRY)]
    commitIndex,         \* [NODE -> Nat]
    lastApplied,         \* [NODE -> Nat]
    snapshotLastIndex,   \* [NODE -> Nat]
    snapshotLastTerm,    \* [NODE -> Nat]
    snapshotInProgress,  \* [NODE -> BOOLEAN]
    nextSnapshotLastIndex, \* [NODE -> Nat]
    nextSnapshotLastTerm,  \* [NODE -> Nat]
    electionElapsed,     \* [NODE -> Nat]
    electionTimeout,     \* [NODE -> Nat]
    heartbeatElapsed,    \* [NODE -> Nat]
    votesPrevote,        \* [NODE -> Nat]
    votesGranted,        \* [NODE -> Nat]
    matchIndex,          \* [NODE -> [NODE -> Nat]]
    nextIndex,           \* [NODE -> [NODE -> Nat]]
    msgs                 \* SUBSET of messages

vars == <<NodeSet, VotingSet, state, currentTerm, votedFor, leaderRef, log, commitIndex, lastApplied,
          snapshotLastIndex, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIndex, nextSnapshotLastTerm,
          electionElapsed, electionTimeout, heartbeatElapsed, votesPrevote, votesGranted, matchIndex, nextIndex, msgs>>

Messages ==
    { m \in [
        mtype: MsgType,
        src: NODE, dst: NODE,
        term: Nat,
        prevote: BOOLEAN,
        requestTerm: Nat,
        voteGranted: BOOLEAN,
        candidateId: NODE \cup {Nil},
        lastLogIndex: Nat,
        lastLogTerm: Nat,
        leaderId: NODE \cup {Nil},
        prevLogIndex: Nat,
        prevLogTerm: Nat,
        leaderCommit: Nat,
        entries: Seq(ENTRY),
        success: BOOLEAN,
        currentIdx: Nat,
        snapshotIndex: Nat,
        snapshotTerm: Nat
      ]:
      TRUE }

TypeInvariant ==
    /\ NodeSet \subseteq NODE
    /\ VotingSet \subseteq NodeSet
    /\ state \in [NODE -> STATES]
    /\ currentTerm \in [NODE -> Nat]
    /\ votedFor \in [NODE -> NODE \cup {Nil}]
    /\ leaderRef \in [NODE -> NODE \cup {Nil}]
    /\ log \in [NODE -> Seq(ENTRY)]
    /\ commitIndex \in [NODE -> Nat]
    /\ lastApplied \in [NODE -> Nat]
    /\ snapshotLastIndex \in [NODE -> Nat]
    /\ snapshotLastTerm \in [NODE -> Nat]
    /\ snapshotInProgress \in [NODE -> BOOLEAN]
    /\ nextSnapshotLastIndex \in [NODE -> Nat]
    /\ nextSnapshotLastTerm \in [NODE -> Nat]
    /\ electionElapsed \in [NODE -> Nat]
    /\ electionTimeout \in [NODE -> Nat]
    /\ heartbeatElapsed \in [NODE -> Nat]
    /\ votesPrevote \in [NODE -> Nat]
    /\ votesGranted \in [NODE -> Nat]
    /\ matchIndex \in [NODE -> [NODE -> Nat]]
    /\ nextIndex \in [NODE -> [NODE -> Nat]]
    /\ \A n \in NODE: \A m \in NODE: matchIndex[n][m] \in Nat /\ nextIndex[n][m] \in Nat
    /\ msgs \subseteq Messages

Quorum(S) == (Cardinality(S) \div 2) + 1

LastIndex(n) == snapshotLastIndex[n] + Len(log[n])

IndexToPos(n, i) == IF i = 0 THEN 0 ELSE i - snapshotLastIndex[n]

HasEntryAt(n, i) == (i = 0) \/ (i > snapshotLastIndex[n] /\ i <= LastIndex(n))

TermAtIndex(n, i) ==
    IF i = 0 THEN snapshotLastTerm[n]
    ELSE IF i <= snapshotLastIndex[n] THEN snapshotLastTerm[n]
    ELSE log[n][IndexToPos(n, i)].term

EntryAtIndex(n, i) ==
    IF i = 0 THEN [term |-> snapshotLastTerm[n], type |-> NOOP, node |-> Nil]
    ELSE log[n][IndexToPos(n, i)]

UpToDate(reqLastTerm, reqLastIndex, n) ==
    /\ reqLastTerm > TermAtIndex(n, LastIndex(n))
    \/ (reqLastTerm = TermAtIndex(n, LastIndex(n)) /\ reqLastIndex >= LastIndex(n))

AppendLog(n, es) == log[n] \o es

DeleteFromIdx(n, idx) ==
    IF idx <= snapshotLastIndex[n] THEN log[n]
    ELSE SubSeq(log[n], 1, IndexToPos(n, idx))

ResetElectionTimer(n) ==
    /\ electionElapsed' = [electionElapsed EXCEPT ![n] = 0]
    /\ \E et \in TimeoutRange: electionTimeout' = [electionTimeout EXCEPT ![n] = et]
    /\ UNCHANGED <<heartbeatElapsed>>

SameTimers == /\ UNCHANGED <<electionElapsed, electionTimeout, heartbeatElapsed>>

MsgsWithout(m) == msgs \ {m}

Enq(m) == msgs' = msgs \cup {m}
Deq(m) == msgs' = msgs \ {m}

Init ==
    /\ NodeSet = InitNodeSet
    /\ VotingSet = InitVotingSet
    /\ state = [n \in NODE |-> IF n \in NodeSet THEN FOLLOWER ELSE FOLLOWER]
    /\ currentTerm = [n \in NODE |-> 0]
    /\ votedFor = [n \in NODE |-> Nil]
    /\ leaderRef = [n \in NODE |-> Nil]
    /\ log = [n \in NODE |-> << >>]
    /\ commitIndex = [n \in NODE |-> 0]
    /\ lastApplied = [n \in NODE |-> 0]
    /\ snapshotLastIndex = [n \in NODE |-> 0]
    /\ snapshotLastTerm = [n \in NODE |-> 0]
    /\ snapshotInProgress = [n \in NODE |-> FALSE]
    /\ nextSnapshotLastIndex = [n \in NODE |-> 0]
    /\ nextSnapshotLastTerm = [n \in NODE |-> 0]
    /\ \E etset \in [NODE -> TimeoutRange]: electionTimeout = etset
    /\ electionElapsed = [n \in NODE |-> 0]
    /\ heartbeatElapsed = [n \in NODE |-> 0]
    /\ votesPrevote = [n \in NODE |-> 0]
    /\ votesGranted = [n \in NODE |-> 0]
    /\ matchIndex = [l \in NODE |-> [p \in NODE |-> 0]]
    /\ nextIndex = [l \in NODE |-> [p \in NODE |-> 1]]
    /\ msgs = {}

PeriodicElectionTimeout ==
    \E n \in NodeSet:
        /\ state[n] # LEADER
        /\ electionElapsed' = [electionElapsed EXCEPT ![n] = electionElapsed[n] + 1]
        /\ UNCHANGED <<NodeSet, VotingSet, state, currentTerm, votedFor, leaderRef, log, commitIndex,
                      lastApplied, snapshotLastIndex, snapshotLastTerm, snapshotInProgress,
                      nextSnapshotLastIndex, nextSnapshotLastTerm, electionTimeout, heartbeatElapsed,
                      votesPrevote, votesGranted, matchIndex, nextIndex, msgs>>

PeriodicHeartbeat ==
    \E l \in NodeSet:
        /\ state[l] = LEADER
        /\ heartbeatElapsed' = [heartbeatElapsed EXCEPT ![l] = heartbeatElapsed[l] + 1]
        /\ UNCHANGED <<NodeSet, VotingSet, state, currentTerm, votedFor, leaderRef, log, commitIndex,
                      lastApplied, snapshotLastIndex, snapshotLastTerm, snapshotInProgress,
                      nextSnapshotLastIndex, nextSnapshotLastTerm, electionElapsed, electionTimeout,
                      votesPrevote, votesGranted, matchIndex, nextIndex, msgs>>

ElectionStart ==
    \E n \in NodeSet:
        /\ state[n] # LEADER
        /\ electionElapsed[n] >= electionTimeout[n]
        /\ state' = [state EXCEPT ![n] = PRECANDIDATE]
        /\ votesPrevote' = [votesPrevote EXCEPT ![n] = (IF n \in VotingSet THEN 1 ELSE 0)]
        /\ votesGranted' = votesGranted
        /\ msgs' = msgs \cup { [mtype |-> ReqVote,
                                src |-> n, dst |-> v,
                                term |-> currentTerm[n] + 1,
                                prevote |-> TRUE,
                                requestTerm |-> currentTerm[n] + 1,
                                voteGranted |-> FALSE,
                                candidateId |-> n,
                                lastLogIndex |-> LastIndex(n),
                                lastLogTerm |-> TermAtIndex(n, LastIndex(n)),
                                leaderId |-> Nil,
                                prevLogIndex |-> 0,
                                prevLogTerm |-> 0,
                                leaderCommit |-> 0,
                                entries |-> << >>,
                                success |-> FALSE,
                                currentIdx |-> 0,
                                snapshotIndex |-> 0,
                                snapshotTerm |-> 0] : v \in VotingSet \ {n} }
        /\ ResetElectionTimer(n)
        /\ UNCHANGED <<NodeSet, VotingSet, currentTerm, votedFor, leaderRef, log, commitIndex,
                      lastApplied, snapshotLastIndex, snapshotLastTerm, snapshotInProgress,
                      nextSnapshotLastIndex, nextSnapshotLastTerm, heartbeatElapsed,
                      matchIndex, nextIndex>>

ElectionTimeout ==
    \E n \in NodeSet:
        /\ state[n] # LEADER
        /\ electionElapsed[n] >= electionTimeout[n]
        /\ state' = [state EXCEPT ![n] = PRECANDIDATE]
        /\ votesPrevote' = [votesPrevote EXCEPT ![n] = (IF n \in VotingSet THEN 1 ELSE 0)]
        /\ votesGranted' = votesGranted
        /\ msgs' = msgs \cup { [mtype |-> ReqVote,
                                src |-> n, dst |-> v,
                                term |-> currentTerm[n] + 1,
                                prevote |-> TRUE,
                                requestTerm |-> currentTerm[n] + 1,
                                voteGranted |-> FALSE,
                                candidateId |-> n,
                                lastLogIndex |-> LastIndex(n),
                                lastLogTerm |-> TermAtIndex(n, LastIndex(n)),
                                leaderId |-> Nil,
                                prevLogIndex |-> 0,
                                prevLogTerm |-> 0,
                                leaderCommit |-> 0,
                                entries |-> << >>,
                                success |-> FALSE,
                                currentIdx |-> 0,
                                snapshotIndex |-> 0,
                                snapshotTerm |-> 0] : v \in VotingSet \ {n} }
        /\ ResetElectionTimer(n)
        /\ UNCHANGED <<NodeSet, VotingSet, currentTerm, votedFor, leaderRef, log, commitIndex,
                      lastApplied, snapshotLastIndex, snapshotLastTerm, snapshotInProgress,
                      nextSnapshotLastIndex, nextSnapshotLastTerm, heartbeatElapsed,
                      matchIndex, nextIndex>>

BecomePreCandidate ==
    \E n \in NodeSet:
        /\ state[n] # LEADER
        /\ state[n] # PRECANDIDATE
        /\ state' = [state EXCEPT ![n] = PRECANDIDATE]
        /\ votesPrevote' = [votesPrevote EXCEPT ![n] = (IF n \in VotingSet THEN 1 ELSE 0)]
        /\ msgs' = msgs \cup { [mtype |-> ReqVote,
                                src |-> n, dst |-> v,
                                term |-> currentTerm[n] + 1,
                                prevote |-> TRUE,
                                requestTerm |-> currentTerm[n] + 1,
                                voteGranted |-> FALSE,
                                candidateId |-> n,
                                lastLogIndex |-> LastIndex(n),
                                lastLogTerm |-> TermAtIndex(n, LastIndex(n)),
                                leaderId |-> Nil,
                                prevLogIndex |-> 0,
                                prevLogTerm |-> 0,
                                leaderCommit |-> 0,
                                entries |-> << >>,
                                success |-> FALSE,
                                currentIdx |-> 0,
                                snapshotIndex |-> 0,
                                snapshotTerm |-> 0] : v \in VotingSet \ {n} }
        /\ ResetElectionTimer(n)
        /\ UNCHANGED <<NodeSet, VotingSet, currentTerm, votedFor, leaderRef, log, commitIndex,
                      lastApplied, snapshotLastIndex, snapshotLastTerm, snapshotInProgress,
                      nextSnapshotLastIndex, nextSnapshotLastTerm, electionElapsed,
                      heartbeatElapsed, votesGranted, matchIndex, nextIndex>>

BecomeCandidate ==
    \E n \in NodeSet:
        /\ state[n] = PRECANDIDATE
        /\ votesPrevote[n] >= Quorum(VotingSet)
        /\ state' = [state EXCEPT ![n] = CANDIDATE]
        /\ currentTerm' = [currentTerm EXCEPT ![n] = currentTerm[n] + 1]
        /\ votedFor' = [votedFor EXCEPT ![n] = IF n \in VotingSet THEN n ELSE votedFor[n]]
        /\ votesGranted' = [votesGranted EXCEPT ![n] = IF n \in VotingSet THEN 1 ELSE 0]
        /\ votesPrevote' = votesPrevote
        /\ msgs' = msgs \cup { [mtype |-> ReqVote,
                                src |-> n, dst |-> v,
                                term |-> currentTerm[n] + 1,
                                prevote |-> FALSE,
                                requestTerm |-> currentTerm[n] + 1,
                                voteGranted |-> FALSE,
                                candidateId |-> n,
                                lastLogIndex |-> LastIndex(n),
                                lastLogTerm |-> TermAtIndex(n, LastIndex(n)),
                                leaderId |-> Nil,
                                prevLogIndex |-> 0,
                                prevLogTerm |-> 0,
                                leaderCommit |-> 0,
                                entries |-> << >>,
                                success |-> FALSE,
                                currentIdx |-> 0,
                                snapshotIndex |-> 0,
                                snapshotTerm |-> 0] : v \in VotingSet \ {n} }
        /\ ResetElectionTimer(n)
        /\ UNCHANGED <<NodeSet, VotingSet, leaderRef, log, commitIndex, lastApplied,
                      snapshotLastIndex, snapshotLastTerm, snapshotInProgress,
                      nextSnapshotLastIndex, nextSnapshotLastTerm, heartbeatElapsed,
                      matchIndex, nextIndex>>

BecomeLeader ==
    \E n \in NodeSet:
        /\ state[n] = CANDIDATE
        /\ votesGranted[n] >= Quorum(VotingSet)
        /\ state' = [state EXCEPT ![n] = LEADER]
        /\ leaderRef' = [leaderRef EXCEPT ![n] = n]
        /\ log' = [log EXCEPT ![n] = AppendLog(n, << [term |-> currentTerm[n], type |-> NOOP, node |-> Nil] >>)]
        /\ commitIndex' = commitIndex
        /\ lastApplied' = lastApplied
        /\ matchIndex' = [matchIndex EXCEPT ![n] = [matchIndex[n] EXCEPT ![n] = LastIndex(n) + 1]]
        /\ nextIndex' = [nextIndex EXCEPT ![n] = [p \in NODE |-> LastIndex(n) + 1]]
        /\ msgs' = msgs \cup { [mtype |-> AppEnt, src |-> n, dst |-> f, term |-> currentTerm[n], prevote |-> FALSE, requestTerm |-> currentTerm[n],
                                voteGranted |-> FALSE, candidateId |-> Nil, lastLogIndex |-> 0, lastLogTerm |-> 0,
                                leaderId |-> n, prevLogIndex |-> LastIndex(n), prevLogTerm |-> TermAtIndex(n, LastIndex(n)),
                                leaderCommit |-> commitIndex[n], entries |-> << >>, success |-> FALSE, currentIdx |-> 0,
                                snapshotIndex |-> snapshotLastIndex[n], snapshotTerm |-> snapshotLastTerm[n] ] : f \in NodeSet \ {n} }
        /\ heartbeatElapsed' = [heartbeatElapsed EXCEPT ![n] = 0]
        /\ votesPrevote' = votesPrevote
        /\ votesGranted' = votesGranted
        /\ UNCHANGED <<NodeSet, VotingSet, currentTerm, votedFor, snapshotLastIndex, snapshotLastTerm,
                      snapshotInProgress, nextSnapshotLastIndex, nextSnapshotLastTerm, electionElapsed, electionTimeout>>

BecomeFollower ==
    \E n \in NodeSet:
        /\ state[n] # FOLLOWER
        /\ state' = [state EXCEPT ![n] = FOLLOWER]
        /\ leaderRef' = [leaderRef EXCEPT ![n] = Nil]
        /\ ResetElectionTimer(n)
        /\ UNCHANGED <<NodeSet, VotingSet, currentTerm, votedFor, log, commitIndex, lastApplied,
                      snapshotLastIndex, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIndex,
                      nextSnapshotLastTerm, heartbeatElapsed, votesPrevote, votesGranted, matchIndex, nextIndex, msgs>>

SendAppendEntries ==
    \E l \in NodeSet, f \in NodeSet:
        /\ state[l] = LEADER
        /\ f # l
        /\ f \in NodeSet
        /\ nextIndex[l][f] <= LastIndex(l) + 1
        /\ LET start == nextIndex[l][f]
               es == IF start <= LastIndex(l) THEN SubSeq(log[l], IndexToPos(l, start), Len(log[l])) ELSE << >>
               prevIdx == start - 1
               prevTerm == TermAtIndex(l, prevIdx)
               m == [mtype |-> AppEnt, src |-> l, dst |-> f, term |-> currentTerm[l], prevote |-> FALSE, requestTerm |-> currentTerm[l],
                     voteGranted |-> FALSE, candidateId |-> Nil, lastLogIndex |-> 0, lastLogTerm |-> 0,
                     leaderId |-> l, prevLogIndex |-> prevIdx, prevLogTerm |-> prevTerm,
                     leaderCommit |-> commitIndex[l], entries |-> es, success |-> FALSE, currentIdx |-> 0,
                     snapshotIndex |-> snapshotLastIndex[l], snapshotTerm |-> snapshotLastTerm[l] ]
           IN msgs' = msgs \cup {m}
        /\ UNCHANGED <<NodeSet, VotingSet, state, currentTerm, votedFor, leaderRef, log, commitIndex,
                      lastApplied, snapshotLastIndex, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIndex,
                      nextSnapshotLastTerm, electionElapsed, electionTimeout, heartbeatElapsed, votesPrevote,
                      votesGranted, matchIndex, nextIndex>>

SendHeartbeat ==
    \E l \in NodeSet, f \in NodeSet:
        /\ state[l] = LEADER
        /\ heartbeatElapsed[l] >= REQUEST_TIMEOUT
        /\ f # l
        /\ LET start == nextIndex[l][f]
               prevIdx == start - 1
               prevTerm == TermAtIndex(l, prevIdx)
               m == [mtype |-> AppEnt, src |-> l, dst |-> f, term |-> currentTerm[l], prevote |-> FALSE, requestTerm |-> currentTerm[l],
                     voteGranted |-> FALSE, candidateId |-> Nil, lastLogIndex |-> 0, lastLogTerm |-> 0,
                     leaderId |-> l, prevLogIndex |-> prevIdx, prevLogTerm |-> prevTerm,
                     leaderCommit |-> commitIndex[l], entries |-> << >>, success |-> FALSE, currentIdx |-> 0,
                     snapshotIndex |-> snapshotLastIndex[l], snapshotTerm |-> snapshotLastTerm[l] ]
           IN /\ msgs' = msgs \cup {m}
              /\ heartbeatElapsed' = [heartbeatElapsed EXCEPT ![l] = 0]
        /\ UNCHANGED <<NodeSet, VotingSet, state, currentTerm, votedFor, leaderRef, log, commitIndex,
                      lastApplied, snapshotLastIndex, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIndex,
                      nextSnapshotLastTerm, electionElapsed, electionTimeout, votesPrevote, votesGranted, matchIndex, nextIndex>>

RecvAppendEntries ==
    \E m \in msgs:
        /\ m.mtype = AppEnt
        /\ m.dst \in NodeSet
        /\ LET n == m.dst IN
           /\ IF m.term < currentTerm[n] THEN
                 /\ msgs' = (msgs \ {m}) \cup {
                        [mtype |-> AppEntResp, src |-> n, dst |-> m.src, term |-> currentTerm[n],
                         prevote |-> FALSE, requestTerm |-> m.term, voteGranted |-> FALSE, candidateId |-> Nil,
                         lastLogIndex |-> 0, lastLogTerm |-> 0, leaderId |-> Nil, prevLogIndex |-> 0, prevLogTerm |-> 0,
                         leaderCommit |-> 0, entries |-> << >>, success |-> FALSE, currentIdx |-> LastIndex(n),
                         snapshotIndex |-> 0, snapshotTerm |-> 0] }
                 /\ UNCHANGED <<NodeSet, VotingSet, state, currentTerm, votedFor, leaderRef, log, commitIndex,
                               lastApplied, snapshotLastIndex, snapshotLastTerm, snapshotInProgress,
                               nextSnapshotLastIndex, nextSnapshotLastTerm, electionElapsed, electionTimeout,
                               heartbeatElapsed, votesPrevote, votesGranted, matchIndex, nextIndex>>
              ELSE
                 /\ currentTerm' = [currentTerm EXCEPT ![n] = m.term]
                 /\ state' = [state EXCEPT ![n] = FOLLOWER]
                 /\ leaderRef' = [leaderRef EXCEPT ![n] = m.src]
                 /\ electionElapsed' = [electionElapsed EXCEPT ![n] = 0]
                 /\ \E et \in TimeoutRange: electionTimeout' = [electionTimeout EXCEPT ![n] = et]
                 /\ log' =
                      [log EXCEPT ![n] =
                        IF ~HasEntryAt(n, m.prevLogIndex) \/ TermAtIndex(n, m.prevLogIndex) # m.prevLogTerm
                        THEN log[n]
                        ELSE
                          LET cutoff == IndexToPos(n, m.prevLogIndex)
                              kept == SubSeq(log[n], 1, cutoff)
                              appd == m.entries
                          IN kept \o appd]
                 /\ commitIndex' =
                      [commitIndex EXCEPT ![n] =
                        IF commitIndex[n] < m.leaderCommit
                        THEN min(LastIndex(n) + Len(m.entries), m.leaderCommit)
                        ELSE commitIndex[n]]
                 /\ msgs' = (msgs \ {m}) \cup {
                        [mtype |-> AppEntResp, src |-> n, dst |-> m.src, term |-> m.term,
                         prevote |-> FALSE, requestTerm |-> m.term, voteGranted |-> FALSE, candidateId |-> Nil,
                         lastLogIndex |-> 0, lastLogTerm |-> 0, leaderId |-> Nil, prevLogIndex |-> 0, prevLogTerm |-> 0,
                         leaderCommit |-> 0, entries |-> << >>,
                         success |-> HasEntryAt(n, m.prevLogIndex) /\ (TermAtIndex(n, m.prevLogIndex) = m.prevLogTerm),
                         currentIdx |-> IF Len(m.entries) = 0 THEN m.prevLogIndex ELSE m.prevLogIndex + Len(m.entries),
                         snapshotIndex |-> 0, snapshotTerm |-> 0] }
                 /\ UNCHANGED <<NodeSet, VotingSet, votedFor, snapshotLastIndex, snapshotLastTerm, snapshotInProgress,
                               nextSnapshotLastIndex, nextSnapshotLastTerm, heartbeatElapsed, votesPrevote,
                               votesGranted, matchIndex, nextIndex>>

LogCommit(leader) ==
    /\ \E nc \in 0..LastIndex(leader):
         /\ nc \in 0..LastIndex(leader)
         /\ Cardinality({ v \in VotingSet: (v = leader /\ LastIndex(leader) >= nc) \/ (matchIndex[leader][v] >= nc) }) >= Quorum(VotingSet)
         /\ TermAtIndex(leader, nc) = currentTerm[leader]
         /\ commitIndex' = [commitIndex EXCEPT ![leader] = max(commitIndex[leader], nc)]
    \/ /\ commitIndex' = commitIndex

RecvAppendEntriesResponse ==
    \E m \in msgs:
        /\ m.mtype = AppEntResp
        /\ m.dst \in NodeSet
        /\ LET n == m.dst IN
           /\ state[n] = LEADER
           /\ IF m.term > currentTerm[n] THEN
                 /\ currentTerm' = [currentTerm EXCEPT ![n] = m.term]
                 /\ state' = [state EXCEPT ![n] = FOLLOWER]
                 /\ leaderRef' = [leaderRef EXCEPT ![n] = Nil]
                 /\ ResetElectionTimer(n)
                 /\ msgs' = msgs \ {m}
                 /\ UNCHANGED <<NodeSet, VotingSet, votedFor, log, commitIndex, lastApplied,
                               snapshotLastIndex, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIndex,
                               nextSnapshotLastTerm, heartbeatElapsed, votesPrevote, votesGranted, matchIndex, nextIndex>>
              ELSE
                 /\ IF ~m.success THEN
                        /\ nextIndex' = [nextIndex EXCEPT ![n] = [nextIndex[n] EXCEPT ![m.src] = max(1, m.currentIdx + 1)]]
                        /\ msgs' = msgs \ {m}
                        /\ UNCHANGED <<NodeSet, VotingSet, state, currentTerm, votedFor, leaderRef, log, commitIndex,
                                      lastApplied, snapshotLastIndex, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIndex,
                                      nextSnapshotLastTerm, electionElapsed, electionTimeout, heartbeatElapsed, votesPrevote,
                                      votesGranted, matchIndex>>
                    ELSE
                        /\ matchIndex' = [matchIndex EXCEPT ![n] = [matchIndex[n] EXCEPT ![m.src] = max(matchIndex[n][m.src], m.currentIdx)]]
                        /\ nextIndex' = [nextIndex EXCEPT ![n] = [nextIndex[n] EXCEPT ![m.src] = max(nextIndex[n][m.src], m.currentIdx + 1)]]
                        /\ msgs' = msgs \ {m}
                        /\ UNCHANGED <<NodeSet, VotingSet, state, currentTerm, votedFor, leaderRef, log, lastApplied,
                                      snapshotLastIndex, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIndex,
                                      nextSnapshotLastTerm, electionElapsed, electionTimeout, heartbeatElapsed, votesPrevote, votesGranted>>
                        /\ LogCommit(n)

RecvRequestVote ==
    \E m \in msgs:
        /\ m.mtype = ReqVote
        /\ m.dst \in NodeSet
        /\ LET n == m.dst IN
           /\ LET newTerm == IF (~m.prevote /\ m.term > currentTerm[n]) THEN m.term ELSE currentTerm[n]
                  upToDate == UpToDate(m.lastLogTerm, m.lastLogIndex, n)
                  grant ==
                    IF m.prevote THEN
                        ( (leaderRef[n] = Nil \/ electionElapsed[n] >= electionTimeout[n] \/ leaderRef[n] = m.candidateId)
                          /\ upToDate )
                    ELSE
                        ( (m.term = currentTerm[n]) /\ (votedFor[n] \in {Nil, m.candidateId})
                          /\ upToDate )
                  resp == [mtype |-> ReqVoteResp, src |-> n, dst |-> m.src, term |-> newTerm,
                           prevote |-> m.prevote, requestTerm |-> m.term, voteGranted |-> grant,
                           candidateId |-> m.candidateId, lastLogIndex |-> LastIndex(n), lastLogTerm |-> TermAtIndex(n, LastIndex(n)),
                           leaderId |-> Nil, prevLogIndex |-> 0, prevLogTerm |-> 0, leaderCommit |-> 0, entries |-> << >>,
                           success |-> FALSE, currentIdx |-> 0, snapshotIndex |-> 0, snapshotTerm |-> 0]
              IN
                 /\ msgs' = (msgs \ {m}) \cup {resp}
                 /\ IF ~m.prevote /\ m.term > currentTerm[n] THEN
                        /\ currentTerm' = [currentTerm EXCEPT ![n] = m.term]
                        /\ state' = [state EXCEPT ![n] = FOLLOWER]
                        /\ leaderRef' = [leaderRef EXCEPT ![n] = Nil]
                    ELSE
                        /\ UNCHANGED <<currentTerm, state, leaderRef>>
                 /\ votedFor' =
                        IF ~m.prevote /\ grant
                        THEN [votedFor EXCEPT ![n] = m.candidateId]
                        ELSE IF ~m.prevote /\ m.term > currentTerm[n]
                             THEN [votedFor EXCEPT ![n] = Nil]
                             ELSE votedFor
                 /\ IF (~m.prevote /\ grant) \/ (~m.prevote /\ m.term > currentTerm[n])
                    THEN ResetElectionTimer(n)
                    ELSE SameTimers
                 /\ UNCHANGED <<NodeSet, VotingSet, log, commitIndex, lastApplied, snapshotLastIndex, snapshotLastTerm,
                               snapshotInProgress, nextSnapshotLastIndex, nextSnapshotLastTerm, heartbeatElapsed,
                               votesPrevote, votesGranted, matchIndex, nextIndex>>

RecvRequestVoteResponse ==
    \E m \in msgs:
        /\ m.mtype = ReqVoteResp
        /\ m.dst \in NodeSet
        /\ LET n == m.dst IN
           /\ IF m.term > currentTerm[n] THEN
                 /\ currentTerm' = [currentTerm EXCEPT ![n] = m.term]
                 /\ state' = [state EXCEPT ![n] = FOLLOWER]
                 /\ leaderRef' = [leaderRef EXCEPT ![n] = Nil]
                 /\ ResetElectionTimer(n)
                 /\ msgs' = msgs \ {m}
                 /\ UNCHANGED <<NodeSet, VotingSet, votedFor, log, commitIndex, lastApplied, snapshotLastIndex, snapshotLastTerm,
                               snapshotInProgress, nextSnapshotLastIndex, nextSnapshotLastTerm, heartbeatElapsed,
                               votesPrevote, votesGranted, matchIndex, nextIndex>>
              ELSE
                 /\ msgs' = msgs \ {m}
                 /\ IF m.prevote /\ state[n] = PRECANDIDATE /\ m.requestTerm = currentTerm[n] + 1 /\ m.voteGranted THEN
                        /\ votesPrevote' = [votesPrevote EXCEPT ![n] = votesPrevote[n] + 1]
                        /\ UNCHANGED <<NodeSet, VotingSet, state, currentTerm, votedFor, leaderRef, log, commitIndex,
                                      lastApplied, snapshotLastIndex, snapshotLastTerm, snapshotInProgress,
                                      nextSnapshotLastIndex, nextSnapshotLastTerm, electionElapsed, electionTimeout,
                                      heartbeatElapsed, votesGranted, matchIndex, nextIndex>>
                    ELSE IF ~m.prevote /\ state[n] = CANDIDATE /\ m.requestTerm = currentTerm[n] /\ m.voteGranted THEN
                        /\ votesGranted' = [votesGranted EXCEPT ![n] = votesGranted[n] + 1]
                        /\ UNCHANGED <<NodeSet, VotingSet, state, currentTerm, votedFor, leaderRef, log, commitIndex,
                                      lastApplied, snapshotLastIndex, snapshotLastTerm, snapshotInProgress,
                                      nextSnapshotLastIndex, nextSnapshotLastTerm, electionElapsed, electionTimeout,
                                      heartbeatElapsed, votesPrevote, matchIndex, nextIndex>>
                    ELSE
                        /\ UNCHANGED <<NodeSet, VotingSet, state, currentTerm, votedFor, leaderRef, log, commitIndex,
                                      lastApplied, snapshotLastIndex, snapshotLastTerm, snapshotInProgress,
                                      nextSnapshotLastIndex, nextSnapshotLastTerm, electionElapsed, electionTimeout,
                                      heartbeatElapsed, votesPrevote, votesGranted, matchIndex, nextIndex>>

LogAppend ==
    \E n \in NodeSet:
        /\ state[n] = LEADER
        /\ log' = [log EXCEPT ![n] = AppendLog(n, << [term |-> currentTerm[n], type |-> NORMAL, node |-> Nil] >>)]
        /\ matchIndex' = [matchIndex EXCEPT ![n] = [matchIndex[n] EXCEPT ![n] = LastIndex(n) + 1]]
        /\ UNCHANGED <<NodeSet, VotingSet, state, currentTerm, votedFor, leaderRef, commitIndex, lastApplied,
                      snapshotLastIndex, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIndex,
                      nextSnapshotLastTerm, electionElapsed, electionTimeout, heartbeatElapsed, votesPrevote,
                      votesGranted, nextIndex, msgs>>

LogDelete ==
    \E n \in NodeSet, idx \in 0..LastIndex(n):
        /\ state[n] # LEADER
        /\ idx > snapshotLastIndex[n]
        /\ idx > commitIndex[n]
        /\ idx <= LastIndex(n)
        /\ log' = [log EXCEPT ![n] = SubSeq(log[n], 1, IndexToPos(n, idx - 1))]
        /\ UNCHANGED <<NodeSet, VotingSet, state, currentTerm, votedFor, leaderRef, commitIndex, lastApplied,
                      snapshotLastIndex, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIndex,
                      nextSnapshotLastTerm, electionElapsed, electionTimeout, heartbeatElapsed, votesPrevote,
                      votesGranted, matchIndex, nextIndex, msgs>>

AddNode ==
    \E l \in NodeSet, x \in NODE \ NodeSet:
        /\ state[l] = LEADER
        /\ log' = [log EXCEPT ![l] = AppendLog(l, << [term |-> currentTerm[l], type |-> ADD_NODE, node |-> x] >>)]
        /\ UNCHANGED <<NodeSet, VotingSet, state, currentTerm, votedFor, leaderRef, commitIndex, lastApplied,
                      snapshotLastIndex, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIndex,
                      nextSnapshotLastTerm, electionElapsed, electionTimeout, heartbeatElapsed, votesPrevote,
                      votesGranted, matchIndex, nextIndex, msgs>>

RemoveNode ==
    \E l \in NodeSet, x \in NodeSet:
        /\ state[l] = LEADER
        /\ x # l
        /\ log' = [log EXCEPT ![l] = AppendLog(l, << [term |-> currentTerm[l], type |-> REMOVE_NODE, node |-> x] >>)]
        /\ UNCHANGED <<NodeSet, VotingSet, state, currentTerm, votedFor, leaderRef, commitIndex, lastApplied,
                      snapshotLastIndex, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIndex,
                      nextSnapshotLastTerm, electionElapsed, electionTimeout, heartbeatElapsed, votesPrevote,
                      votesGranted, matchIndex, nextIndex, msgs>>

ApplyConfigChange ==
    \E n \in NodeSet:
        /\ lastApplied[n] < commitIndex[n]
        /\ LET nextIdx == lastApplied[n] + 1
               e == EntryAtIndex(n, nextIdx)
           IN /\ e.type \in {ADD_NODE, ADD_NONVOTING_NODE, REMOVE_NODE}
              /\ IF e.type = ADD_NODE THEN
                    /\ NodeSet' = NodeSet \cup {e.node}
                    /\ VotingSet' = VotingSet \cup {e.node}
                 ELSE IF e.type = ADD_NONVOTING_NODE THEN
                    /\ NodeSet' = NodeSet \cup {e.node}
                    /\ VotingSet' = VotingSet
                 ELSE
                    /\ NodeSet' = NodeSet \ {e.node}
                    /\ VotingSet' = VotingSet \ {e.node}
        /\ lastApplied' = [lastApplied EXCEPT ![n] = lastApplied[n] + 1]
        /\ UNCHANGED <<state, currentTerm, votedFor, leaderRef, log, commitIndex, snapshotLastIndex, snapshotLastTerm,
                      snapshotInProgress, nextSnapshotLastIndex, nextSnapshotLastTerm, electionElapsed, electionTimeout,
                      heartbeatElapsed, votesPrevote, votesGranted, matchIndex, nextIndex, msgs>>

SnapshotBegin ==
    \E n \in NodeSet:
        /\ ~snapshotInProgress[n]
        /\ lastApplied[n] - snapshotLastIndex[n] >= SNAPSHOT_THRESHOLD
        /\ snapshotInProgress' = [snapshotInProgress EXCEPT ![n] = TRUE]
        /\ nextSnapshotLastIndex' = [nextSnapshotLastIndex EXCEPT ![n] = lastApplied[n]]
        /\ nextSnapshotLastTerm' = [nextSnapshotLastTerm EXCEPT ![n] = TermAtIndex(n, lastApplied[n])]
        /\ UNCHANGED <<NodeSet, VotingSet, state, currentTerm, votedFor, leaderRef, log, commitIndex, lastApplied,
                      snapshotLastIndex, snapshotLastTerm, electionElapsed, electionTimeout, heartbeatElapsed, votesPrevote,
                      votesGranted, matchIndex, nextIndex, msgs>>

SnapshotEnd ==
    \E n \in NodeSet:
        /\ snapshotInProgress[n]
        /\ snapshotInProgress' = [snapshotInProgress EXCEPT ![n] = FALSE]
        /\ snapshotLastIndex' = [snapshotLastIndex EXCEPT ![n] = nextSnapshotLastIndex[n]]
        /\ snapshotLastTerm' = [snapshotLastTerm EXCEPT ![n] = nextSnapshotLastTerm[n]]
        /\ log' =
            [log EXCEPT ![n] =
                IF nextSnapshotLastIndex[n] <= snapshotLastIndex[n]
                THEN log[n]
                ELSE SubSeq(log[n], IndexToPos(n, nextSnapshotLastIndex[n] + 1), Len(log[n]))]
        /\ UNCHANGED <<NodeSet, VotingSet, state, currentTerm, votedFor, leaderRef, commitIndex, lastApplied,
                      nextSnapshotLastIndex, nextSnapshotLastTerm, electionElapsed, electionTimeout,
                      heartbeatElapsed, votesPrevote, votesGranted, matchIndex, nextIndex, msgs>>

LogCommitNoop ==
    \E n \in NodeSet:
        /\ state[n] = LEADER
        /\ UNCHANGED <<NodeSet, VotingSet, state, currentTerm, votedFor, leaderRef, log, lastApplied,
                      snapshotLastIndex, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIndex,
                      nextSnapshotLastTerm, electionElapsed, electionTimeout, heartbeatElapsed, votesPrevote,
                      votesGranted, matchIndex, nextIndex, msgs>>
        /\ LogCommit(n)

ApplyNonConfig ==
    \E n \in NodeSet:
        /\ lastApplied[n] < commitIndex[n]
        /\ EntryAtIndex(n, lastApplied[n] + 1).type \notin {ADD_NODE, ADD_NONVOTING_NODE, REMOVE_NODE}
        /\ lastApplied' = [lastApplied EXCEPT ![n] = lastApplied[n] + 1]
        /\ UNCHANGED <<NodeSet, VotingSet, state, currentTerm, votedFor, leaderRef, log, commitIndex, snapshotLastIndex,
                      snapshotLastTerm, snapshotInProgress, nextSnapshotLastIndex, nextSnapshotLastTerm, electionElapsed,
                      electionTimeout, heartbeatElapsed, votesPrevote, votesGranted, matchIndex, nextIndex, msgs>>

Next ==
    \/ PeriodicElectionTimeout
    \/ PeriodicHeartbeat
    \/ ElectionTimeout
    \/ ElectionStart
    \/ BecomePreCandidate
    \/ BecomeCandidate
    \/ BecomeLeader
    \/ BecomeFollower
    \/ SendAppendEntries
    \/ SendHeartbeat
    \/ RecvAppendEntries
    \/ RecvAppendEntriesResponse
    \/ RecvRequestVote
    \/ RecvRequestVoteResponse
    \/ LogAppend
    \/ LogDelete
    \/ LogCommitNoop
    \/ AddNode
    \/ RemoveNode
    \/ ApplyConfigChange
    \/ ApplyNonConfig
    \/ SnapshotBegin
    \/ SnapshotEnd

Spec ==
    Init /\ [][Next]_vars

====