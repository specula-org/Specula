---- MODULE redisraft ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Nodes, ELECTION_TIMEOUT, REQUEST_TIMEOUT

Null == "Null"

EntryType == {"noop","cmd","add","add_nonvoting","remove"}

VARIABLES
    state,
    currentTerm,
    votedFor,
    log,
    baseIndex,
    baseTerm,
    commitIndex,
    lastApplied,
    leaderId,
    electionElapsed,
    randomTimeout,
    hbElapsed,
    Members,
    Voters,
    nextIndex,
    matchIndex,
    snapshotInProgress,
    nextSnapIndex,
    nextSnapTerm,
    Net,
    MsgId,
    rvVotes,
    pvVotes,
    appliedConfigIndices

vars == << state, currentTerm, votedFor, log, baseIndex, baseTerm, commitIndex, lastApplied, leaderId, electionElapsed, randomTimeout, hbElapsed, Members, Voters, nextIndex, matchIndex, snapshotInProgress, nextSnapIndex, nextSnapTerm, Net, MsgId, rvVotes, pvVotes, appliedConfigIndices >>

IsFollower(n) == state[n] = "Follower"
IsPreCandidate(n) == state[n] = "PreCandidate"
IsCandidate(n) == state[n] = "Candidate"
IsLeader(n) == state[n] = "Leader"

LastLogIndex(n) == baseIndex[n] + Len(log[n])
LastLogTerm(n) == IF Len(log[n]) = 0 THEN baseTerm[n] ELSE log[n][Len(log[n])].term

HasIndex(n, idx) == idx = baseIndex[n] \/ (baseIndex[n] < idx /\ idx <= LastLogIndex(n))

TermAt(n, idx) ==
    IF idx = baseIndex[n] THEN baseTerm[n]
    ELSE log[n][idx - baseIndex[n]].term

EntryAt(n, idx) ==
    IF baseIndex[n] < idx /\ idx <= LastLogIndex(n) THEN log[n][idx - baseIndex[n]] ELSE [term |-> baseTerm[n], type |-> "noop", node |-> Null]

SeqFromIndex(n, start) ==
    IF start > LastLogIndex(n) THEN <<>>
    ELSE SubSeq(log[n], start - baseIndex[n], Len(log[n]))

DropPrefixToIndex(n, idx) ==
    IF idx <= baseIndex[n] THEN log[n]
    ELSE
        LET k == idx - baseIndex[n]
        IN IF k > Len(log[n]) THEN <<>> ELSE SubSeq(log[n], k + 1, Len(log[n]))

QuorumSize == (Cardinality(Voters) \div 2) + 1

Init ==
    /\ state \in [Nodes -> {"Follower","PreCandidate","Candidate","Leader"}]
    /\ state = [n \in Nodes |-> "Follower"]
    /\ currentTerm \in [Nodes -> Nat]
    /\ currentTerm = [n \in Nodes |-> 0]
    /\ votedFor \in [Nodes -> (Nodes \cup {Null})]
    /\ votedFor = [n \in Nodes |-> Null]
    /\ log \in [Nodes -> Seq([term: Nat, type: EntryType, node: (Nodes \cup {Null})])]
    /\ log = [n \in Nodes |-> <<>>]
    /\ baseIndex \in [Nodes -> Nat]
    /\ baseIndex = [n \in Nodes |-> 0]
    /\ baseTerm \in [Nodes -> Nat]
    /\ baseTerm = [n \in Nodes |-> 0]
    /\ commitIndex \in [Nodes -> Nat]
    /\ commitIndex = [n \in Nodes |-> 0]
    /\ lastApplied \in [Nodes -> Nat]
    /\ lastApplied = [n \in Nodes |-> 0]
    /\ leaderId \in [Nodes -> (Nodes \cup {Null})]
    /\ leaderId = [n \in Nodes |-> Null]
    /\ electionElapsed \in [Nodes -> Nat]
    /\ electionElapsed = [n \in Nodes |-> 0]
    /\ randomTimeout \in [Nodes -> Nat]
    /\ randomTimeout \in [Nodes -> ELECTION_TIMEOUT..(2 * ELECTION_TIMEOUT)]
    /\ hbElapsed \in [Nodes -> Nat]
    /\ hbElapsed = [n \in Nodes |-> 0]
    /\ Members \subseteq Nodes
    /\ Members = Nodes
    /\ Voters \subseteq Members
    /\ Voters = Members
    /\ nextIndex \in [Nodes -> [Nodes -> Nat]]
    /\ nextIndex = [l \in Nodes |-> [p \in Nodes |-> 1]]
    /\ matchIndex \in [Nodes -> [Nodes -> Nat]]
    /\ matchIndex = [l \in Nodes |-> [p \in Nodes |-> 0]]
    /\ snapshotInProgress \in [Nodes -> BOOLEAN]
    /\ snapshotInProgress = [n \in Nodes |-> FALSE]
    /\ nextSnapIndex \in [Nodes -> Nat]
    /\ nextSnapIndex = [n \in Nodes |-> 0]
    /\ nextSnapTerm \in [Nodes -> Nat]
    /\ nextSnapTerm = [n \in Nodes |-> 0]
    /\ Net \subseteq SUBSET {
        [type: "RV", from: Nodes, to: Nodes, term: Nat, prevote: BOOLEAN, lastLogIndex: Nat, lastLogTerm: Nat, id: Nat],
        [type: "RVR", from: Nodes, to: Nodes, term: Nat, prevote: BOOLEAN, voteGranted: BOOLEAN, requestTerm: Nat, id: Nat],
        [type: "AE", from: Nodes, to: Nodes, term: Nat, prevLogIndex: Nat, prevLogTerm: Nat, entries: Seq([term: Nat, type: EntryType, node: (Nodes \cup {Null})]), leaderCommit: Nat, id: Nat],
        [type: "AER", from: Nodes, to: Nodes, term: Nat, success: BOOLEAN, currentIndex: Nat, id: Nat]
    }
    /\ Net = {}
    /\ MsgId \in Nat
    /\ MsgId = 0
    /\ rvVotes \in [Nodes -> SUBSET Nodes]
    /\ rvVotes = [n \in Nodes |-> {}]
    /\ pvVotes \in [Nodes -> SUBSET Nodes]
    /\ pvVotes = [n \in Nodes |-> {}]
    /\ appliedConfigIndices \subseteq Nat
    /\ appliedConfigIndices = {}

BecomeFollower(n) ==
    /\ n \in Nodes
    /\ state' = [state EXCEPT ![n] = "Follower"]
    /\ leaderId' = [leaderId EXCEPT ![n] = Null]
    /\ electionElapsed' = [electionElapsed EXCEPT ![n] = 0]
    /\ randomTimeout' \in [Nodes -> Nat]
    /\ \A x \in Nodes:
        randomTimeout'[x] \in ELECTION_TIMEOUT..(2 * ELECTION_TIMEOUT)
        /\ (x # n => randomTimeout'[x] = randomTimeout[x])
    /\ hbElapsed' = hbElapsed
    /\ currentTerm' = currentTerm
    /\ votedFor' = votedFor
    /\ log' = log
    /\ baseIndex' = baseIndex
    /\ baseTerm' = baseTerm
    /\ commitIndex' = commitIndex
    /\ lastApplied' = lastApplied
    /\ Members' = Members
    /\ Voters' = Voters
    /\ nextIndex' = nextIndex
    /\ matchIndex' = matchIndex
    /\ snapshotInProgress' = snapshotInProgress
    /\ nextSnapIndex' = nextSnapIndex
    /\ nextSnapTerm' = nextSnapTerm
    /\ Net' = Net
    /\ MsgId' = MsgId
    /\ rvVotes' = [rvVotes EXCEPT ![n] = {}]
    /\ pvVotes' = [pvVotes EXCEPT ![n] = {}]
    /\ appliedConfigIndices' = appliedConfigIndices

ElectionStart(n) ==
    /\ n \in Nodes
    /\ ~IsLeader(n)
    /\ electionElapsed[n] >= randomTimeout[n]
    /\ leaderId' = [leaderId EXCEPT ![n] = Null]
    /\ electionElapsed' = [electionElapsed EXCEPT ![n] = 0]
    /\ randomTimeout' \in [Nodes -> Nat]
    /\ \A x \in Nodes:
        randomTimeout'[x] \in ELECTION_TIMEOUT..(2 * ELECTION_TIMEOUT)
        /\ (x # n => randomTimeout'[x] = randomTimeout[x])
    /\ state' = [state EXCEPT ![n] = "PreCandidate"]
    /\ pvVotes' = [pvVotes EXCEPT ![n] = {}]
    /\ rvVotes' = rvVotes
    /\ LET msgs == { [type |-> "RV",
                     from |-> n,
                     to |-> m,
                     term |-> currentTerm[n] + 1,
                     prevote |-> TRUE,
                     lastLogIndex |-> LastLogIndex(n),
                     lastLogTerm |-> LastLogTerm(n),
                     id |-> MsgId + 1 + i]
                    : m \in Voters \cap Members \ {n}
                      /\ i \in 1..Cardinality(Voters \cap Members \ {n}) }
       IN /\ Net' = Net \cup msgs
          /\ MsgId' = MsgId + Cardinality(Voters \cap Members \ {n})
    /\ hbElapsed' = hbElapsed
    /\ currentTerm' = currentTerm
    /\ votedFor' = votedFor
    /\ log' = log
    /\ baseIndex' = baseIndex
    /\ baseTerm' = baseTerm
    /\ commitIndex' = commitIndex
    /\ lastApplied' = lastApplied
    /\ Members' = Members
    /\ Voters' = Voters
    /\ nextIndex' = nextIndex
    /\ matchIndex' = matchIndex
    /\ snapshotInProgress' = snapshotInProgress
    /\ nextSnapIndex' = nextSnapIndex
    /\ nextSnapTerm' = nextSnapTerm
    /\ appliedConfigIndices' = appliedConfigIndices

BecomePreCandidate(n) ==
    /\ n \in Nodes
    /\ state[n] # "PreCandidate"
    /\ state' = [state EXCEPT ![n] = "PreCandidate"]
    /\ pvVotes' = [pvVotes EXCEPT ![n] = {}]
    /\ rvVotes' = rvVotes
    /\ leaderId' = [leaderId EXCEPT ![n] = Null]
    /\ electionElapsed' = [electionElapsed EXCEPT ![n] = 0]
    /\ randomTimeout' = randomTimeout
    /\ LET msgs == { [type |-> "RV",
                     from |-> n,
                     to |-> m,
                     term |-> currentTerm[n] + 1,
                     prevote |-> TRUE,
                     lastLogIndex |-> LastLogIndex(n),
                     lastLogTerm |-> LastLogTerm(n),
                     id |-> MsgId + 1 + i]
                    : m \in Voters \cap Members \ {n}
                      /\ i \in 1..Cardinality(Voters \cap Members \ {n}) }
       IN /\ Net' = Net \cup msgs
          /\ MsgId' = MsgId + Cardinality(Voters \cap Members \ {n})
    /\ hbElapsed' = hbElapsed
    /\ currentTerm' = currentTerm
    /\ votedFor' = votedFor
    /\ log' = log
    /\ baseIndex' = baseIndex
    /\ baseTerm' = baseTerm
    /\ commitIndex' = commitIndex
    /\ lastApplied' = lastApplied
    /\ Members' = Members
    /\ Voters' = Voters
    /\ nextIndex' = nextIndex
    /\ matchIndex' = matchIndex
    /\ snapshotInProgress' = snapshotInProgress
    /\ nextSnapIndex' = nextSnapIndex
    /\ nextSnapTerm' = nextSnapTerm
    /\ appliedConfigIndices' = appliedConfigIndices

BecomeCandidate(n) ==
    /\ n \in Nodes
    /\ IsPreCandidate(n) \/ IsFollower(n) \/ IsCandidate(n)
    /\ currentTerm' = [currentTerm EXCEPT ![n] = currentTerm[n] + 1]
    /\ votedFor' = [votedFor EXCEPT ![n] = n]
    /\ state' = [state EXCEPT ![n] = "Candidate"]
    /\ rvVotes' = [rvVotes EXCEPT ![n] = {n}]
    /\ pvVotes' = [pvVotes EXCEPT ![n] = {}]
    /\ leaderId' = [leaderId EXCEPT ![n] = Null]
    /\ electionElapsed' = [electionElapsed EXCEPT ![n] = 0]
    /\ randomTimeout' = randomTimeout
    /\ LET msgs == { [type |-> "RV",
                     from |-> n,
                     to |-> m,
                     term |-> currentTerm[n] + 1,
                     prevote |-> FALSE,
                     lastLogIndex |-> LastLogIndex(n),
                     lastLogTerm |-> LastLogTerm(n),
                     id |-> MsgId + 1 + i]
                    : m \in Voters \cap Members \ {n}
                      /\ i \in 1..Cardinality(Voters \cap Members \ {n}) }
       IN /\ Net' = Net \cup msgs
          /\ MsgId' = MsgId + Cardinality(Voters \cap Members \ {n})
    /\ hbElapsed' = hbElapsed
    /\ log' = log
    /\ baseIndex' = baseIndex
    /\ baseTerm' = baseTerm
    /\ commitIndex' = commitIndex
    /\ lastApplied' = lastApplied
    /\ Members' = Members
    /\ Voters' = Voters
    /\ nextIndex' = nextIndex
    /\ matchIndex' = matchIndex
    /\ snapshotInProgress' = snapshotInProgress
    /\ nextSnapIndex' = nextSnapIndex
    /\ nextSnapTerm' = nextSnapTerm
    /\ appliedConfigIndices' = appliedConfigIndices

BecomeLeader(n) ==
    /\ n \in Nodes
    /\ IsCandidate(n)
    /\ Cardinality(rvVotes[n] \cap Voters) >= QuorumSize
    /\ state' = [state EXCEPT ![n] = "Leader"]
    /\ leaderId' = [leaderId EXCEPT ![n] = n]
    /\ hbElapsed' = [hbElapsed EXCEPT ![n] = 0]
    /\ electionElapsed' = [electionElapsed EXCEPT ![n] = 0]
    /\ randomTimeout' = randomTimeout
    /\ LET noop == [term |-> currentTerm[n], type |-> "noop", node |-> Null]
       IN log' = [log EXCEPT ![n] = Append(@, noop)]
    /\ baseIndex' = baseIndex
    /\ baseTerm' = baseTerm
    /\ currentTerm' = currentTerm
    /\ votedFor' = votedFor
    /\ commitIndex' =
        [commitIndex EXCEPT ![n] =
            IF Cardinality(Voters) = 1 /\ n \in Voters THEN LastLogIndex(n) + 1 ELSE @]
    /\ lastApplied' = lastApplied
    /\ nextIndex' = [nextIndex EXCEPT ![n] = [p \in Nodes |-> LastLogIndex(n) + 2]]
    /\ matchIndex' = [matchIndex EXCEPT ![n] = [p \in Nodes |-> IF p = n THEN LastLogIndex(n) + 1 ELSE 0]]
    /\ Members' = Members
    /\ Voters' = Voters
    /\ snapshotInProgress' = snapshotInProgress
    /\ nextSnapIndex' = nextSnapIndex
    /\ nextSnapTerm' = nextSnapTerm
    /\ Net' = Net
    /\ MsgId' = MsgId
    /\ rvVotes' = [rvVotes EXCEPT ![n] = {}]
    /\ pvVotes' = [pvVotes EXCEPT ![n] = {}]
    /\ appliedConfigIndices' = appliedConfigIndices

SendAppendEntries(l, f) ==
    /\ l \in Nodes /\ f \in Nodes /\ l # f
    /\ IsLeader(l)
    /\ f \in Members
    /\ nextIndex[l][f] <= LastLogIndex(l) + 1
    /\ LET start == nextIndex[l][f]
           prevIdx == start - 1
           prevTm == TermAt(l, prevIdx)
           ents == SeqFromIndex(l, start)
           msg == [type |-> "AE",
                   from |-> l,
                   to |-> f,
                   term |-> currentTerm[l],
                   prevLogIndex |-> prevIdx,
                   prevLogTerm |-> prevTm,
                   entries |-> ents,
                   leaderCommit |-> commitIndex[l],
                   id |-> MsgId + 1]
       IN /\ Net' = Net \cup {msg}
          /\ MsgId' = MsgId + 1
          /\ UNCHANGED << state, currentTerm, votedFor, log, baseIndex, baseTerm, commitIndex, lastApplied, leaderId, electionElapsed, randomTimeout, hbElapsed, Members, Voters, nextIndex, matchIndex, snapshotInProgress, nextSnapIndex, nextSnapTerm, rvVotes, pvVotes, appliedConfigIndices >>

SendHeartbeat(l, f) ==
    /\ l \in Nodes /\ f \in Nodes /\ l # f
    /\ IsLeader(l)
    /\ f \in Members
    /\ LET prevIdx == LastLogIndex(l)
           prevTm == TermAt(l, prevIdx)
           msg == [type |-> "AE",
                   from |-> l,
                   to |-> f,
                   term |-> currentTerm[l],
                   prevLogIndex |-> prevIdx,
                   prevLogTerm |-> prevTm,
                   entries |-> <<>>,
                   leaderCommit |-> commitIndex[l],
                   id |-> MsgId + 1]
       IN /\ Net' = Net \cup {msg}
          /\ MsgId' = MsgId + 1
          /\ UNCHANGED << state, currentTerm, votedFor, log, baseIndex, baseTerm, commitIndex, lastApplied, leaderId, electionElapsed, randomTimeout, hbElapsed, Members, Voters, nextIndex, matchIndex, snapshotInProgress, nextSnapIndex, nextSnapTerm, rvVotes, pvVotes, appliedConfigIndices >>

RecvAppendEntries ==
    \E m \in Net:
      /\ m.type = "AE"
      /\ LET r == m.to
             l == m.from
             t == m.term
             okTerm == t >= currentTerm[r]
             matchPrev == HasIndex(r, m.prevLogIndex)
                           /\ TermAt(r, m.prevLogIndex) = m.prevLogTerm
             deleteFrom ==
                 IF m.entries = <<>> THEN LastLogIndex(r) + 1
                 ELSE m.prevLogIndex + 1
             newLog ==
                 IF ~matchPrev THEN log[r]
                 ELSE
                   LET delPos == deleteFrom
                       keepSeq == DropPrefixToIndex(r, delPos)
                       prefixLen == delPos - baseIndex[r] - 1
                       headSeq ==
                           IF prefixLen <= 0 THEN <<>> ELSE SubSeq(log[r], 1, prefixLen)
                       appended == m.entries
                   IN AppendSeqs(headSeq, appended)
             lastAppendedIndex ==
                 IF ~matchPrev THEN IF LastLogIndex(r) = 0 THEN 0 ELSE LastLogIndex(r)
                 ELSE IF Len(m.entries) = 0 THEN m.prevLogIndex
                      ELSE m.prevLogIndex + Len(m.entries)
             AppendSeqs(s1, s2) == 
                 IF Len(s1) = 0 THEN s2
                 ELSE [i \in 1..(Len(s1) + Len(s2)) |->
                        IF i <= Len(s1) THEN s1[i] ELSE s2[i - Len(s1)]]
         IN /\ IF t > currentTerm[r] THEN currentTerm' = [currentTerm EXCEPT ![r] = t] ELSE currentTerm' = currentTerm
            /\ IF t > currentTerm[r] THEN state' = [state EXCEPT ![r] = "Follower"] ELSE state' = state
            /\ leaderId' = [leaderId EXCEPT ![r] = l]
            /\ electionElapsed' = [electionElapsed EXCEPT ![r] = 0]
            /\ randomTimeout' = randomTimeout
            /\ IF okTerm /\ matchPrev THEN log' = [log EXCEPT ![r] = newLog] ELSE log' = log
            /\ baseIndex' = baseIndex
            /\ baseTerm' = baseTerm
            /\ commitIndex' =
                  [commitIndex EXCEPT ![r] =
                      IF okTerm /\ matchPrev THEN
                          IF m.leaderCommit > commitIndex[r] THEN
                              IF LastLogIndex(r)' > 0 THEN
                                  Min(m.leaderCommit, LastLogIndex(r)')
                              ELSE m.leaderCommit
                          ELSE commitIndex[r]
                      ELSE commitIndex[r]]
            /\ lastApplied' = lastApplied
            /\ Members' = Members
            /\ Voters' = Voters
            /\ nextIndex' = nextIndex
            /\ matchIndex' = matchIndex
            /\ snapshotInProgress' = snapshotInProgress
            /\ nextSnapIndex' = nextSnapIndex
            /\ nextSnapTerm' = nextSnapTerm
            /\ Net' =
                LET resp == [type |-> "AER",
                             from |-> r,
                             to |-> l,
                             term |-> IF t >= currentTerm[r] THEN currentTerm'[r] ELSE currentTerm[r],
                             success |-> okTerm /\ matchPrev,
                             currentIndex |-> IF okTerm /\ matchPrev THEN lastAppendedIndex ELSE LastLogIndex(r),
                             id |-> MsgId + 1]
                IN (Net \ {m}) \cup {resp}
            /\ MsgId' = MsgId + 1
            /\ rvVotes' = rvVotes
            /\ pvVotes' = pvVotes
            /\ appliedConfigIndices' = appliedConfigIndices

RecvAppendEntriesResponse ==
    \E m \in Net:
      /\ m.type = "AER"
      /\ LET l == m.to
             f == m.from
         IN /\ IsLeader(l)
            /\ IF m.term > currentTerm[l] THEN
                  /\ currentTerm' = [currentTerm EXCEPT ![l] = m.term]
                  /\ state' = [state EXCEPT ![l] = "Follower"]
                  /\ leaderId' = [leaderId EXCEPT ![l] = Null]
               ELSE
                  /\ currentTerm' = currentTerm
                  /\ state' = state
                  /\ leaderId' = leaderId
            /\ electionElapsed' = electionElapsed
            /\ randomTimeout' = randomTimeout
            /\ hbElapsed' = hbElapsed
            /\ nextIndex' =
                 IF m.term > currentTerm[l] THEN nextIndex
                 ELSE
                   [nextIndex EXCEPT ![l] = [p \in Nodes |->
                       IF p # f THEN @ [p] ELSE IF m.success THEN m.currentIndex + 1
                       ELSE Max(1, Min(m.currentIndex + 1, LastLogIndex(l) + 1))]]
            /\ matchIndex' =
                 IF m.term > currentTerm[l] THEN matchIndex
                 ELSE
                   [matchIndex EXCEPT ![l] = [p \in Nodes |->
                       IF p # f THEN @ [p] ELSE IF m.success THEN Max(@[p], m.currentIndex) ELSE @[p]]]
            /\ LET idxs == { i \in Nat :
                                i <= LastLogIndex(l)
                                /\ i > commitIndex[l]
                                /\ TermAt(l, i) = currentTerm[l]
                                /\ Cardinality({p \in Voters : IF p = l THEN LastLogIndex(l) >= i ELSE matchIndex'[l][p] >= i}) >= QuorumSize }
               IN commitIndex' = [commitIndex EXCEPT ![l] =
                                    IF m.term > currentTerm[l] THEN @
                                    ELSE IF idxs = {} THEN @ ELSE Max(idxs)]
            /\ log' = log
            /\ baseIndex' = baseIndex
            /\ baseTerm' = baseTerm
            /\ lastApplied' = lastApplied
            /\ Members' = Members
            /\ Voters' = Voters
            /\ snapshotInProgress' = snapshotInProgress
            /\ nextSnapIndex' = nextSnapIndex
            /\ nextSnapTerm' = nextSnapTerm
            /\ Net' = Net \ {m}
            /\ MsgId' = MsgId
            /\ rvVotes' = rvVotes
            /\ pvVotes' = pvVotes
            /\ appliedConfigIndices' = appliedConfigIndices

RecvRequestVote ==
    \E m \in Net:
      /\ m.type = "RV"
      /\ LET r == m.to
             c == m.from
             isPrevote == m.prevote
             t == m.term
             upToDate == m.lastLogTerm > LastLogTerm(r)
                         \/ (m.lastLogTerm = LastLogTerm(r) /\ m.lastLogIndex >= LastLogIndex(r))
             hasLeaderWhenPrevote == isPrevote /\ leaderId[r] # Null /\ electionElapsed[r] < ELECTION_TIMEOUT
             grant == ~hasLeaderWhenPrevote
                      /\ (t >= currentTerm[r])
                      /\ (isPrevote \/ votedFor[r] = Null \/ votedFor[r] = c)
                      /\ upToDate
             newTerm == IF ~isPrevote /\ t > currentTerm[r] THEN t ELSE currentTerm[r]
             resp == [type |-> "RVR",
                      from |-> r,
                      to |-> c,
                      term |-> IF ~isPrevote THEN newTerm ELSE currentTerm[r],
                      prevote |-> isPrevote,
                      voteGranted |-> grant,
                      requestTerm |-> t,
                      id |-> MsgId + 1]
         IN /\ currentTerm' = [currentTerm EXCEPT ![r] = newTerm]
            /\ state' = [state EXCEPT ![r] = IF ~isPrevote /\ t >= currentTerm[r] THEN "Follower" ELSE @]
            /\ leaderId' = [leaderId EXCEPT ![r] = IF ~isPrevote /\ grant THEN Null ELSE @]
            /\ electionElapsed' = [electionElapsed EXCEPT ![r] = IF ~isPrevote /\ grant THEN 0 ELSE @]
            /\ randomTimeout' = randomTimeout
            /\ votedFor' = [votedFor EXCEPT ![r] = IF ~isPrevote /\ grant THEN c ELSE @]
            /\ log' = log
            /\ baseIndex' = baseIndex
            /\ baseTerm' = baseTerm
            /\ commitIndex' = commitIndex
            /\ lastApplied' = lastApplied
            /\ Members' = Members
            /\ Voters' = Voters
            /\ nextIndex' = nextIndex
            /\ matchIndex' = matchIndex
            /\ snapshotInProgress' = snapshotInProgress
            /\ nextSnapIndex' = nextSnapIndex
            /\ nextSnapTerm' = nextSnapTerm
            /\ Net' = (Net \ {m}) \cup {resp}
            /\ MsgId' = MsgId + 1
            /\ rvVotes' = rvVotes
            /\ pvVotes' = pvVotes
            /\ appliedConfigIndices' = appliedConfigIndices

RecvRequestVoteResponse ==
    \E m \in Net:
      /\ m.type = "RVR"
      /\ LET n == m.to
         IN /\ IF m.term > currentTerm[n] THEN
                  /\ currentTerm' = [currentTerm EXCEPT ![n] = m.term]
                  /\ state' = [state EXCEPT ![n] = "Follower"]
                  /\ leaderId' = [leaderId EXCEPT ![n] = Null]
               ELSE
                  /\ currentTerm' = currentTerm
                  /\ state' = state
                  /\ leaderId' = leaderId
            /\ electionElapsed' = electionElapsed
            /\ randomTimeout' = randomTimeout
            /\ hbElapsed' = hbElapsed
            /\ votedFor' = votedFor
            /\ IF m.prevote THEN
                 /\ IsPreCandidate(n)
                 /\ m.requestTerm = currentTerm[n] + 1
                 /\ pvVotes' = [pvVotes EXCEPT ![n] = IF m.voteGranted /\ m.from \in Voters THEN @ \cup {m.from} ELSE @]
                 /\ rvVotes' = rvVotes
               ELSE
                 /\ IsCandidate(n)
                 /\ m.requestTerm = currentTerm[n]
                 /\ rvVotes' = [rvVotes EXCEPT ![n] = IF m.voteGranted /\ m.from \in Voters THEN @ \cup {m.from} ELSE @]
                 /\ pvVotes' = pvVotes
            /\ log' = log
            /\ baseIndex' = baseIndex
            /\ baseTerm' = baseTerm
            /\ commitIndex' = commitIndex
            /\ lastApplied' = lastApplied
            /\ Members' = Members
            /\ Voters' = Voters
            /\ nextIndex' = nextIndex
            /\ matchIndex' = matchIndex
            /\ snapshotInProgress' = snapshotInProgress
            /\ nextSnapIndex' = nextSnapIndex
            /\ nextSnapTerm' = nextSnapTerm
            /\ Net' = Net \ {m}
            /\ MsgId' = MsgId
            /\ appliedConfigIndices' = appliedConfigIndices

LogAppend(n, etype, targetNode) ==
    /\ n \in Nodes
    /\ IsLeader(n)
    /\ etype \in EntryType
    /\ targetNode \in (Nodes \cup {Null})
    /\ IF etype \in {"add","add_nonvoting","remove"} THEN targetNode \in Nodes ELSE TRUE
    /\ log' = [log EXCEPT ![n] = Append(@, [term |-> currentTerm[n], type |-> etype, node |-> targetNode])]
    /\ UNCHANGED << state, currentTerm, votedFor, baseIndex, baseTerm, commitIndex, lastApplied, leaderId, electionElapsed, randomTimeout, hbElapsed, Members, Voters, nextIndex, matchIndex, snapshotInProgress, nextSnapIndex, nextSnapTerm, Net, MsgId, rvVotes, pvVotes, appliedConfigIndices >>

LogDelete(n, idx) ==
    /\ n \in Nodes
    /\ ~IsLeader(n)
    /\ HasIndex(n, idx)
    /\ idx > baseIndex[n]
    /\ log' = [log EXCEPT ![n] = SubSeq(@, 1, idx - baseIndex[n] - 1)]
    /\ UNCHANGED << state, currentTerm, votedFor, baseIndex, baseTerm, commitIndex, lastApplied, leaderId, electionElapsed, randomTimeout, hbElapsed, Members, Voters, nextIndex, matchIndex, snapshotInProgress, nextSnapIndex, nextSnapTerm, Net, MsgId, rvVotes, pvVotes, appliedConfigIndices >>

LogCommit(l) ==
    /\ l \in Nodes
    /\ IsLeader(l)
    /\ LET idxs == { i \in Nat :
                      i > commitIndex[l] /\ i <= LastLogIndex(l)
                      /\ TermAt(l, i) = currentTerm[l]
                      /\ Cardinality({p \in Voters : IF p = l THEN LastLogIndex(l) >= i ELSE matchIndex[l][p] >= i}) >= QuorumSize }
       IN commitIndex' = [commitIndex EXCEPT ![l] = IF idxs = {} THEN @ ELSE Max(idxs)]
    /\ UNCHANGED << state, currentTerm, votedFor, log, baseIndex, baseTerm, lastApplied, leaderId, electionElapsed, randomTimeout, hbElapsed, Members, Voters, nextIndex, matchIndex, snapshotInProgress, nextSnapIndex, nextSnapTerm, Net, MsgId, rvVotes, pvVotes, appliedConfigIndices >>

Apply(n) ==
    /\ n \in Nodes
    /\ lastApplied[n] < commitIndex[n]
    /\ LET idx == lastApplied[n] + 1
           e == EntryAt(n, idx)
       IN /\ lastApplied' = [lastApplied EXCEPT ![n] = idx]
          /\ IF e.type \in {"add","add_nonvoting","remove"} /\ ~(idx \in appliedConfigIndices) THEN
                /\ ApplyConfigChangeEffect(e)
                /\ appliedConfigIndices' = appliedConfigIndices \cup {idx}
             ELSE
                /\ appliedConfigIndices' = appliedConfigIndices
          /\ UNCHANGED << state, currentTerm, votedFor, log, baseIndex, baseTerm, commitIndex, leaderId, electionElapsed, randomTimeout, hbElapsed, nextIndex, matchIndex, snapshotInProgress, nextSnapIndex, nextSnapTerm, Net, MsgId, rvVotes, pvVotes, Members, Voters >>

ApplyConfigChangeEffect(e) ==
    IF e.type = "add" THEN
        /\ Members' = Members \cup {e.node}
        /\ Voters' = Voters \cup {e.node}
    ELSE IF e.type = "add_nonvoting" THEN
        /\ Members' = Members \cup {e.node}
        /\ Voters' = Voters
    ELSE IF e.type = "remove" THEN
        /\ Members' = Members \ {e.node}
        /\ Voters' = Voters \ {e.node}
    ELSE /\ Members' = Members /\ Voters' = Voters

AddNode(n, u) ==
    /\ n \in Nodes /\ u \in Nodes /\ u \notin Members
    /\ LogAppend(n, "add", u)

RemoveNode(n, u) ==
    /\ n \in Nodes /\ u \in Nodes /\ u \in Members /\ u # n
    /\ LogAppend(n, "remove", u)

SnapshotBegin(n) ==
    /\ n \in Nodes
    /\ ~snapshotInProgress[n]
    /\ commitIndex[n] > baseIndex[n]
    /\ lastApplied[n] = commitIndex[n]
    /\ snapshotInProgress' = [snapshotInProgress EXCEPT ![n] = TRUE]
    /\ nextSnapIndex' = [nextSnapIndex EXCEPT ![n] = lastApplied[n]]
    /\ nextSnapTerm' = [nextSnapTerm EXCEPT ![n] = TermAt(n, lastApplied[n])]
    /\ UNCHANGED << state, currentTerm, votedFor, log, baseIndex, baseTerm, commitIndex, lastApplied, leaderId, electionElapsed, randomTimeout, hbElapsed, Members, Voters, nextIndex, matchIndex, Net, MsgId, rvVotes, pvVotes, appliedConfigIndices >>

SnapshotEnd(n) ==
    /\ n \in Nodes
    /\ snapshotInProgress[n]
    /\ baseIndex' = [baseIndex EXCEPT ![n] = nextSnapIndex[n]]
    /\ baseTerm' = [baseTerm EXCEPT ![n] = nextSnapTerm[n]]
    /\ log' = [log EXCEPT ![n] = DropPrefixToIndex(n, nextSnapIndex[n])]
    /\ snapshotInProgress' = [snapshotInProgress EXCEPT ![n] = FALSE]
    /\ UNCHANGED << state, currentTerm, votedFor, commitIndex, lastApplied, leaderId, electionElapsed, randomTimeout, hbElapsed, Members, Voters, nextIndex, matchIndex, nextSnapIndex, nextSnapTerm, Net, MsgId, rvVotes, pvVotes, appliedConfigIndices >>

PeriodicElectionTimeout ==
    \E n \in Nodes:
      /\ ~IsLeader(n)
      /\ electionElapsed' = [electionElapsed EXCEPT ![n] = electionElapsed[n] + 1]
      /\ UNCHANGED << state, currentTerm, votedFor, log, baseIndex, baseTerm, commitIndex, lastApplied, leaderId, randomTimeout, hbElapsed, Members, Voters, nextIndex, matchIndex, snapshotInProgress, nextSnapIndex, nextSnapTerm, Net, MsgId, rvVotes, pvVotes, appliedConfigIndices >>

PeriodicHeartbeat ==
    \E n \in Nodes:
      /\ IsLeader(n)
      /\ hbElapsed[n] >= REQUEST_TIMEOUT
      /\ hbElapsed' = [hbElapsed EXCEPT ![n] = 0]
      /\ LET ms == { [type |-> "AE",
                      from |-> n,
                      to |-> m,
                      term |-> currentTerm[n],
                      prevLogIndex |-> LastLogIndex(n),
                      prevLogTerm |-> TermAt(n, LastLogIndex(n)),
                      entries |-> <<>>,
                      leaderCommit |-> commitIndex[n],
                      id |-> MsgId + 1 + i]
                     : m \in Members \ {n}
                       /\ i \in 1..Cardinality(Members \ {n}) }
         IN /\ Net' = Net \cup ms
            /\ MsgId' = MsgId + Cardinality(Members \ {n})
      /\ UNCHANGED << state, currentTerm, votedFor, log, baseIndex, baseTerm, commitIndex, lastApplied, leaderId, electionElapsed, randomTimeout, Members, Voters, nextIndex, matchIndex, snapshotInProgress, nextSnapIndex, nextSnapTerm, rvVotes, pvVotes, appliedConfigIndices >>

ElectionTimeout ==
    \E n \in Nodes: ElectionStart(n)

Next ==
    \/ PeriodicElectionTimeout
    \/ PeriodicHeartbeat
    \/ ElectionTimeout
    \/ BecomePreCandidate(\E n \in Nodes: n)
    \/ BecomeCandidate(\E n \in Nodes: n)
    \/ BecomeLeader(\E n \in Nodes: n)
    \/ BecomeFollower(\E n \in Nodes: n)
    \/ \E l,f \in Nodes: SendAppendEntries(l,f)
    \/ \E l,f \in Nodes: SendHeartbeat(l,f)
    \/ RecvAppendEntries
    \/ RecvAppendEntriesResponse
    \/ RecvRequestVote
    \/ RecvRequestVoteResponse
    \/ \E n \in Nodes, et \in EntryType, u \in (Nodes \cup {Null}): LogAppend(n, et, u)
    \/ \E n \in Nodes, idx \in Nat: LogDelete(n, idx)
    \/ \E l \in Nodes: LogCommit(l)
    \/ \E n \in Nodes: Apply(n)
    \/ \E n \in Nodes, u \in Nodes: AddNode(n, u)
    \/ \E n \in Nodes, u \in Nodes: RemoveNode(n, u)
    \/ \E n \in Nodes: SnapshotBegin(n)
    \/ \E n \in Nodes: SnapshotEnd(n)

Spec ==
    Init /\ [][Next]_vars

====