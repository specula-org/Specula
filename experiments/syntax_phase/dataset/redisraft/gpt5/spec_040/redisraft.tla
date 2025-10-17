---- MODULE redisraft ----
EXTENDS TLC, Sequences, Naturals, FiniteSets

CONSTANTS
    NODES,
    InitMembers,
    InitVoters,
    None,
    ELECTION_TIMEOUT_BASE,
    REQUEST_TIMEOUT

ASSUME InitVoters \subseteq InitMembers
ASSUME InitMembers \subseteq NODES
ASSUME None \notin NODES

States == {"FOLLOWER","PRECANDIDATE","CANDIDATE","LEADER"}
EntryTypes == {"NOOP","NORMAL","ADD_NODE","ADD_NONVOTING_NODE","REMOVE_NODE"}

Entry == [term: Nat, type: EntryTypes, node: NODES \cup {None}]

VARIABLES
    Members,
    Voters,
    State,
    Term,
    VotedFor,
    LeaderOf,
    Log,
    CommitIndex,
    LastApplied,
    SnapshotIndex,
    SnapshotTerm,
    NextIndex,
    MatchIndex,
    ElectionElapsed,
    ElectionTimeoutRand,
    HBElapsed,
    Net,
    MsgId,
    Votes,
    PreVotes

Message ==
    [ id: Nat,
      type: {"RequestVote","RequestVoteResp","AppendEntries","AppendEntriesResp"},
      from: NODES, to: NODES,
      term: Nat,
      prevote: BOOLEAN,
      candidate: NODES \cup {None},
      lastLogIndex: Nat,
      lastLogTerm: Nat,
      voteGranted: BOOLEAN,
      prevLogIndex: Nat,
      prevLogTerm: Nat,
      entries: Seq(Entry),
      leaderCommit: Nat,
      success: BOOLEAN,
      currentIndex: Nat,
      isHeartbeat: BOOLEAN ]

IsMember(n) == n \in Members
IsVoter(n) == n \in Voters

QuorumSize == Cardinality(Voters) \div 2 + 1

LogLen(n) == Len(Log[n])
LastIndex(n) == SnapshotIndex[n] + LogLen(n)

HasEntryAt(n, i) ==
    /\ i > SnapshotIndex[n]
    /\ (i - SnapshotIndex[n]) \in 1..Len(Log[n])

TermAt(n, i) ==
    IF i = SnapshotIndex[n] THEN SnapshotTerm[n]
    ELSE IF HasEntryAt(n, i) THEN Log[n][i - SnapshotIndex[n]]["term"]
    ELSE 0

SuffixFrom(n, i) ==
    IF i <= SnapshotIndex[n] THEN Log[n]
    ELSE IF i = LastIndex(n) + 1 THEN <<>>
    ELSE IF i > LastIndex(n) + 1 THEN <<>>
    ELSE SubSeq(Log[n], i - SnapshotIndex[n], Len(Log[n]))

PrefixUpto(n, i) ==
    IF i <= SnapshotIndex[n] THEN <<>>
    ELSE IF i > LastIndex(n) THEN Log[n]
    ELSE SubSeq(Log[n], 1, i - SnapshotIndex[n])

AppendEntriesOf(n, entries) == Log[n] \o entries

Min2(a,b) == IF a <= b THEN a ELSE b
Max2(a,b) == IF a >= b THEN a ELSE b

RandomizeTimeout(n) ==
    \E t \in ELECTION_TIMEOUT_BASE..(2*ELECTION_TIMEOUT_BASE):
      ElectionTimeoutRand' = [ElectionTimeoutRand EXCEPT ![n] = t]

ResetTimers(n) ==
    /\ ElectionElapsed' = [ElectionElapsed EXCEPT ![n] = 0]
    /\ HBElapsed' = [HBElapsed EXCEPT ![n] = 0]

ClearVotes(n) ==
    /\ Votes' = [Votes EXCEPT ![n] = {}]
    /\ PreVotes' = [PreVotes EXCEPT ![n] = {}]

Init ==
    /\ Members = InitMembers
    /\ Voters = InitVoters
    /\ State = [n \in NODES |-> "FOLLOWER"]
    /\ Term = [n \in NODES |-> 0]
    /\ VotedFor = [n \in NODES |-> None]
    /\ LeaderOf = [n \in NODES |-> None]
    /\ Log = [n \in NODES |-> <<>>]
    /\ CommitIndex = [n \in NODES |-> 0]
    /\ LastApplied = [n \in NODES |-> 0]
    /\ SnapshotIndex = [n \in NODES |-> 0]
    /\ SnapshotTerm = [n \in NODES |-> 0]
    /\ NextIndex = [l \in NODES |-> [n \in NODES |-> 1]]
    /\ MatchIndex = [l \in NODES |-> [n \in NODES |-> 0]]
    /\ ElectionElapsed = [n \in NODES |-> 0]
    /\ ElectionTimeoutRand = [n \in NODES |-> ELECTION_TIMEOUT_BASE]
    /\ HBElapsed = [n \in NODES |-> 0]
    /\ Net = {}
    /\ MsgId = 0
    /\ Votes = [n \in NODES |-> {}]
    /\ PreVotes = [n \in NODES |-> {}]

BecomeFollower(n) ==
    /\ n \in NODES
    /\ State[n] # "FOLLOWER"
    /\ State' = [State EXCEPT ![n] = "FOLLOWER"]
    /\ LeaderOf' = [LeaderOf EXCEPT ![n] = None]
    /\ ResetTimers(n)
    /\ RandomizeTimeout(n)
    /\ UNCHANGED <<Members,Voters,Term,VotedFor,Log,CommitIndex,LastApplied,SnapshotIndex,SnapshotTerm,NextIndex,MatchIndex,Net,MsgId,Votes,PreVotes>>

BecomePreCandidate(n) ==
    /\ n \in NODES
    /\ IsMember(n)
    /\ State[n] \in {"FOLLOWER","CANDIDATE"}
    /\ State' = [State EXCEPT ![n] = "PRECANDIDATE"]
    /\ LeaderOf' = [LeaderOf EXCEPT ![n] = None]
    /\ \E m \in Members \ {n}:
         /\ IsVoter(m)
         /\ MsgId' = MsgId + 1
         /\ Net' = Net \cup {[
              id |-> MsgId',
              type |-> "RequestVote",
              from |-> n, to |-> m,
              term |-> Term[n] + 1,
              prevote |-> TRUE,
              candidate |-> n,
              lastLogIndex |-> LastIndex(n),
              lastLogTerm |-> TermAt(n, LastIndex(n)),
              voteGranted |-> FALSE,
              prevLogIndex |-> 0,
              prevLogTerm |-> 0,
              entries |-> <<>>,
              leaderCommit |-> 0,
              success |-> FALSE,
              currentIndex |-> 0,
              isHeartbeat |-> FALSE ]}
    /\ ClearVotes(n)
    /\ ResetTimers(n)
    /\ UNCHANGED <<Members,Voters,Term,VotedFor,Log,CommitIndex,LastApplied,SnapshotIndex,SnapshotTerm,NextIndex,MatchIndex,ElectionTimeoutRand>>

BecomeCandidate(n) ==
    /\ n \in NODES
    /\ IsMember(n)
    /\ State[n] \in {"FOLLOWER","PRECANDIDATE"}
    /\ State' = [State EXCEPT ![n] = "CANDIDATE"]
    /\ Term' = [Term EXCEPT ![n] = Term[n] + 1]
    /\ VotedFor' = [VotedFor EXCEPT ![n] = n]
    /\ LeaderOf' = [LeaderOf EXCEPT ![n] = None]
    /\ \E m \in Members \ {n}:
         /\ IsVoter(m)
         /\ MsgId' = MsgId + 1
         /\ Net' = Net \cup {[
              id |-> MsgId',
              type |-> "RequestVote",
              from |-> n, to |-> m,
              term |-> Term[n] + 1,
              prevote |-> FALSE,
              candidate |-> n,
              lastLogIndex |-> LastIndex(n),
              lastLogTerm |-> TermAt(n, LastIndex(n)),
              voteGranted |-> FALSE,
              prevLogIndex |-> 0,
              prevLogTerm |-> 0,
              entries |-> <<>>,
              leaderCommit |-> 0,
              success |-> FALSE,
              currentIndex |-> 0,
              isHeartbeat |-> FALSE ]}
    /\ Votes' = [Votes EXCEPT ![n] = (IF IsVoter(n) THEN {n} ELSE {})]
    /\ PreVotes' = [PreVotes EXCEPT ![n] = {}]
    /\ ResetTimers(n)
    /\ UNCHANGED <<Members,Voters,Log,CommitIndex,LastApplied,SnapshotIndex,SnapshotTerm,NextIndex,MatchIndex,ElectionTimeoutRand>>

BecomeLeader(n) ==
    /\ n \in NODES
    /\ State[n] = "CANDIDATE"
    /\ Cardinality(Votes[n]) >= QuorumSize
    /\ LET newLast == LastIndex(n) + 1 IN
       /\ State' = [State EXCEPT ![n] = "LEADER"]
       /\ LeaderOf' = [LeaderOf EXCEPT ![n] = n]
       /\ Log' = [Log EXCEPT ![n] = AppendEntriesOf(n, << [term |-> Term[n], type |-> "NOOP", node |-> None] >>)]
       /\ NextIndex' = [NextIndex EXCEPT ![n] = [m \in NODES |-> newLast + 1]]
       /\ MatchIndex' = [MatchIndex EXCEPT ![n] = [m \in NODES |-> IF m = n THEN newLast ELSE 0]]
       /\ Votes' = [Votes EXCEPT ![n] = {}]
       /\ PreVotes' = [PreVotes EXCEPT ![n] = {}]
       /\ HBElapsed' = [HBElapsed EXCEPT ![n] = 0]
       /\ UNCHANGED <<Members,Voters,Term,VotedFor,CommitIndex,LastApplied,SnapshotIndex,SnapshotTerm,Net,MsgId,ElectionElapsed,ElectionTimeoutRand>>

ElectionStart(n) ==
    /\ n \in NODES
    /\ State[n] # "LEADER"
    /\ ElectionElapsed[n] >= ElectionTimeoutRand[n]
    /\ LeaderOf' = [LeaderOf EXCEPT ![n] = None]
    /\ ResetTimers(n)
    /\ RandomizeTimeout(n)
    /\ UNCHANGED <<Members,Voters,State,Term,VotedFor,Log,CommitIndex,LastApplied,SnapshotIndex,SnapshotTerm,NextIndex,MatchIndex,Net,MsgId,Votes,PreVotes>>

ElectionTimeout ==
    \E n \in NODES:
      /\ State[n] # "LEADER"
      /\ ElectionElapsed[n] >= ElectionTimeoutRand[n]
      /\ ElectionElapsed' = [ElectionElapsed EXCEPT ![n] = 0]
      /\ RandomizeTimeout(n)
      /\ UNCHANGED <<Members,Voters,State,Term,VotedFor,LeaderOf,Log,CommitIndex,LastApplied,SnapshotIndex,SnapshotTerm,NextIndex,MatchIndex,HBElapsed,Net,MsgId,Votes,PreVotes>>

PeriodicElectionTimeout ==
    \E n \in NODES:
      /\ ElectionElapsed' = [ElectionElapsed EXCEPT ![n] = ElectionElapsed[n] + 1]
      /\ UNCHANGED <<Members,Voters,State,Term,VotedFor,LeaderOf,Log,CommitIndex,LastApplied,SnapshotIndex,SnapshotTerm,NextIndex,MatchIndex,HBElapsed,Net,MsgId,ElectionTimeoutRand,Votes,PreVotes>>

SendHeartbeat ==
    \E l \in NODES, f \in Members \ {l}:
      /\ State[l] = "LEADER"
      /\ MsgId' = MsgId + 1
      /\ Net' = Net \cup {[
          id |-> MsgId',
          type |-> "AppendEntries",
          from |-> l, to |-> f,
          term |-> Term[l],
          prevote |-> FALSE,
          candidate |-> None,
          lastLogIndex |-> 0,
          lastLogTerm |-> 0,
          voteGranted |-> FALSE,
          prevLogIndex |-> Max2(0, NextIndex[l][f] - 1),
          prevLogTerm |-> TermAt(l, Max2(0, NextIndex[l][f] - 1)),
          entries |-> <<>>,
          leaderCommit |-> CommitIndex[l],
          success |-> FALSE,
          currentIndex |-> 0,
          isHeartbeat |-> TRUE ]}
      /\ UNCHANGED <<Members,Voters,State,Term,VotedFor,LeaderOf,Log,CommitIndex,LastApplied,SnapshotIndex,SnapshotTerm,NextIndex,MatchIndex,ElectionElapsed,ElectionTimeoutRand,HBElapsed,Votes,PreVotes>>

PeriodicHeartbeat ==
    \E l \in NODES:
      /\ State[l] = "LEADER"
      /\ HBElapsed' = [HBElapsed EXCEPT ![l] = HBElapsed[l] + 1]
      /\ UNCHANGED <<Members,Voters,State,Term,VotedFor,LeaderOf,Log,CommitIndex,LastApplied,SnapshotIndex,SnapshotTerm,NextIndex,MatchIndex,ElectionElapsed,ElectionTimeoutRand,Net,MsgId,Votes,PreVotes>>

SendAppendEntries ==
    \E l \in NODES, f \in Members \ {l}:
      /\ State[l] = "LEADER"
      /\ NextIndex[l][f] <= LastIndex(l)
      /\ LET entries == SuffixFrom(l, NextIndex[l][f]) IN
         /\ entries # <<>>
         /\ MsgId' = MsgId + 1
         /\ Net' = Net \cup {[
            id |-> MsgId',
            type |-> "AppendEntries",
            from |-> l, to |-> f,
            term |-> Term[l],
            prevote |-> FALSE,
            candidate |-> None,
            lastLogIndex |-> 0,
            lastLogTerm |-> 0,
            voteGranted |-> FALSE,
            prevLogIndex |-> NextIndex[l][f] - 1,
            prevLogTerm |-> TermAt(l, NextIndex[l][f] - 1),
            entries |-> entries,
            leaderCommit |-> CommitIndex[l],
            success |-> FALSE,
            currentIndex |-> 0,
            isHeartbeat |-> FALSE ]}
      /\ UNCHANGED <<Members,Voters,State,Term,VotedFor,LeaderOf,Log,CommitIndex,LastApplied,SnapshotIndex,SnapshotTerm,NextIndex,MatchIndex,ElectionElapsed,ElectionTimeoutRand,HBElapsed,Votes,PreVotes>>

RecvAppendEntries ==
    \E m \in Net:
      /\ m["type"] = "AppendEntries"
      /\ \E n \in NODES: m["to"] = n
      /\ LET newTermN == IF m["term"] > Term[n] THEN m["term"] ELSE Term[n] IN
         /\ Term' = [Term EXCEPT ![n] = newTermN]
         /\ State' = [State EXCEPT ![n] = IF m["term"] > Term[n] THEN "FOLLOWER" ELSE State[n]]
         /\ VotedFor' = [VotedFor EXCEPT ![n] = IF m["term"] > Term[n] THEN None ELSE VotedFor[n]]
      /\ LeaderOf' = [LeaderOf EXCEPT ![n] = m["from"]]
      /\ IF m["term"] < Term'[n] THEN
           /\ Net' = (Net \ {m}) \cup {[
                id |-> MsgId + 1,
                type |-> "AppendEntriesResp",
                from |-> n, to |-> m["from"],
                term |-> Term'[n],
                prevote |-> FALSE,
                candidate |-> None,
                lastLogIndex |-> 0,
                lastLogTerm |-> 0,
                voteGranted |-> FALSE,
                prevLogIndex |-> 0,
                prevLogTerm |-> 0,
                entries |-> <<>>,
                leaderCommit |-> 0,
                success |-> FALSE,
                currentIndex |-> LastIndex(n),
                isHeartbeat |-> FALSE ]}
           /\ MsgId' = MsgId + 1
           /\ UNCHANGED <<Members,Voters,Log,CommitIndex,LastApplied,SnapshotIndex,SnapshotTerm,NextIndex,MatchIndex,ElectionElapsed,ElectionTimeoutRand,HBElapsed,Votes,PreVotes>>
         ELSE
           /\ IF (m["prevLogIndex"] = SnapshotIndex[n] /\ m["prevLogTerm"] = SnapshotTerm[n]) \/
                 (HasEntryAt(n, m["prevLogIndex"]) /\ TermAt(n, m["prevLogIndex"]) = m["prevLogTerm"])
              THEN
                 /\ Log' = [Log EXCEPT ![n] = PrefixUpto(n, m["prevLogIndex"]) \o m["entries"]]
                 /\ LET newLast == m["prevLogIndex"] + Len(m["entries"]) IN
                    CommitIndex' = [CommitIndex EXCEPT ![n] = Min2(newLast, m["leaderCommit"])]
                 /\ Net' = (Net \ {m}) \cup {[
                     id |-> MsgId + 1,
                     type |-> "AppendEntriesResp",
                     from |-> n, to |-> m["from"],
                     term |-> Term'[n],
                     prevote |-> FALSE,
                     candidate |-> None,
                     lastLogIndex |-> 0,
                     lastLogTerm |-> 0,
                     voteGranted |-> FALSE,
                     prevLogIndex |-> 0,
                     prevLogTerm |-> 0,
                     entries |-> <<>>,
                     leaderCommit |-> 0,
                     success |-> TRUE,
                     currentIndex |-> m["prevLogIndex"] + Len(m["entries"]),
                     isHeartbeat |-> FALSE ]}
                 /\ MsgId' = MsgId + 1
                 /\ UNCHANGED <<Members,Voters,LastApplied,SnapshotIndex,SnapshotTerm,NextIndex,MatchIndex,ElectionElapsed,ElectionTimeoutRand,HBElapsed,Votes,PreVotes>>
              ELSE
                 /\ Net' = (Net \ {m}) \cup {[
                     id |-> MsgId + 1,
                     type |-> "AppendEntriesResp",
                     from |-> n, to |-> m["from"],
                     term |-> Term'[n],
                     prevote |-> FALSE,
                     candidate |-> None,
                     lastLogIndex |-> 0,
                     lastLogTerm |-> 0,
                     voteGranted |-> FALSE,
                     prevLogIndex |-> 0,
                     prevLogTerm |-> 0,
                     entries |-> <<>>,
                     leaderCommit |-> 0,
                     success |-> FALSE,
                     currentIndex |-> LastIndex(n),
                     isHeartbeat |-> FALSE ]}
                 /\ MsgId' = MsgId + 1
                 /\ UNCHANGED <<Members,Voters,Log,CommitIndex,LastApplied,SnapshotIndex,SnapshotTerm,NextIndex,MatchIndex,ElectionElapsed,ElectionTimeoutRand,HBElapsed,Votes,PreVotes>>

LogDelete ==
    \E m \in Net:
      /\ m["type"] = "AppendEntries"
      /\ \E n \in NODES:
          /\ m["to"] = n
          /\ HasEntryAt(n, m["prevLogIndex"])
          /\ TermAt(n, m["prevLogIndex"]) # m["prevLogTerm"]
          /\ m["prevLogIndex"] >= CommitIndex[n]
          /\ Log' = [Log EXCEPT ![n] = PrefixUpto(n, m["prevLogIndex"])]
          /\ UNCHANGED <<Members,Voters,State,Term,VotedFor,LeaderOf,CommitIndex,LastApplied,SnapshotIndex,SnapshotTerm,NextIndex,MatchIndex,ElectionElapsed,ElectionTimeoutRand,HBElapsed,Net,MsgId,Votes,PreVotes>>

RecvAppendEntriesResponse ==
    \E m \in Net:
      /\ m["type"] = "AppendEntriesResp"
      /\ \E l \in NODES: m["to"] = l
      /\ State[l] = "LEADER"
      /\ IF m["term"] > Term[l] THEN
           /\ Term' = [Term EXCEPT ![l] = m["term"]]
           /\ State' = [State EXCEPT ![l] = "FOLLOWER"]
           /\ LeaderOf' = [LeaderOf EXCEPT ![l] = None]
           /\ VotedFor' = [VotedFor EXCEPT ![l] = None]
           /\ Net' = Net \ {m}
           /\ UNCHANGED <<Members,Voters,Log,CommitIndex,LastApplied,SnapshotIndex,SnapshotTerm,NextIndex,MatchIndex,ElectionElapsed,ElectionTimeoutRand,HBElapsed,MsgId,Votes,PreVotes>>
         ELSE
           /\ IF m["term"] < Term[l] THEN
                /\ Net' = Net \ {m}
                /\ UNCHANGED <<Members,Voters,State,Term,VotedFor,LeaderOf,Log,CommitIndex,LastApplied,SnapshotIndex,SnapshotTerm,NextIndex,MatchIndex,ElectionElapsed,ElectionTimeoutRand,HBElapsed,MsgId,Votes,PreVotes>>
              ELSE
                /\ IF m["success"] THEN
                     /\ MatchIndex' = [MatchIndex EXCEPT ![l] = [MatchIndex[l] EXCEPT ![(m["from"])] = m["currentIndex"]]]
                     /\ NextIndex' = [NextIndex EXCEPT ![l] = [NextIndex[l] EXCEPT ![(m["from"])] = m["currentIndex"] + 1]]
                     /\ Net' = Net \ {m}
                     /\ UNCHANGED <<Members,Voters,State,Term,VotedFor,LeaderOf,Log,CommitIndex,LastApplied,SnapshotIndex,SnapshotTerm,ElectionElapsed,ElectionTimeoutRand,HBElapsed,MsgId,Votes,PreVotes>>
                   ELSE
                     /\ NextIndex' = [NextIndex EXCEPT ![l] = [NextIndex[l] EXCEPT ![(m["from"])] = Max2(1, NextIndex[l][(m["from"])] - 1)]]
                     /\ Net' = Net \ {m}
                     /\ UNCHANGED <<Members,Voters,State,Term,VotedFor,LeaderOf,Log,CommitIndex,LastApplied,SnapshotIndex,SnapshotTerm,MatchIndex,ElectionElapsed,ElectionTimeoutRand,HBElapsed,MsgId,Votes,PreVotes>>

LogCommit ==
    \/ \E l \in NODES, N \in Nat:
         /\ State[l] = "LEADER"
         /\ N > CommitIndex[l]
         /\ N <= LastIndex(l)
         /\ TermAt(l, N) = Term[l]
         /\ Cardinality({ v \in Voters: (v = l /\ MatchIndex[l][l] >= N) \/ (v # l /\ MatchIndex[l][v] >= N) }) >= QuorumSize
         /\ CommitIndex' = [CommitIndex EXCEPT ![l] = N]
         /\ UNCHANGED <<Members,Voters,State,Term,VotedFor,LeaderOf,Log,LastApplied,SnapshotIndex,SnapshotTerm,NextIndex,MatchIndex,ElectionElapsed,ElectionTimeoutRand,HBElapsed,Net,MsgId,Votes,PreVotes>>
    \/ \E m \in Net:
         /\ m["type"] = "AppendEntries"
         /\ \E n \in NODES: m["to"] = n
         /\ CommitIndex' = [CommitIndex EXCEPT ![n] = Min2(LastIndex(n), m["leaderCommit"])]
         /\ UNCHANGED <<Members,Voters,State,Term,VotedFor,LeaderOf,Log,LastApplied,SnapshotIndex,SnapshotTerm,NextIndex,MatchIndex,ElectionElapsed,ElectionTimeoutRand,HBElapsed,Net,MsgId,Votes,PreVotes>>

LogAppend ==
    \E l \in NODES, t \in EntryTypes, x \in NODES \cup {None}:
      /\ State[l] = "LEADER"
      /\ Log' = [Log EXCEPT ![l] = AppendEntriesOf(l, << [term |-> Term[l], type |-> t, node |-> x] >>)]
      /\ UNCHANGED <<Members,Voters,State,Term,VotedFor,LeaderOf,CommitIndex,LastApplied,SnapshotIndex,SnapshotTerm,NextIndex,MatchIndex,ElectionElapsed,ElectionTimeoutRand,HBElapsed,Net,MsgId,Votes,PreVotes>>

RecvRequestVote ==
    \E m \in Net:
      /\ m["type"] = "RequestVote"
      /\ \E n \in NODES: m["to"] = n
      /\ LET newState ==
              IF ~m["prevote"] /\ m["term"] > Term[n] THEN "FOLLOWER" ELSE State[n]
         IN
         /\ State' = [State EXCEPT ![n] = newState]
      /\ LET newTermN ==
              IF ~m["prevote"] /\ m["term"] > Term[n] THEN m["term"] ELSE Term[n]
         IN
         /\ Term' = [Term EXCEPT ![n] = newTermN]
      /\ LET newVotedFor ==
              IF ~m["prevote"] /\ m["term"] > Term[n] THEN None ELSE VotedFor[n]
         IN
         /\ TRUE
      /\ LET VotedFor_tmp == [VotedFor EXCEPT ![n] = newVotedFor]
             logOk ==
               m["lastLogTerm"] > TermAt(n, LastIndex(n)) \/
               (m["lastLogTerm"] = TermAt(n, LastIndex(n)) /\ m["lastLogIndex"] >= LastIndex(n))
             leaderPresent == (LeaderOf[n] # None) /\ (ElectionElapsed[n] < ElectionTimeoutRand[n])
             canGrant ==
               /\ (m["prevote"] \/ Term'[n] = m["term"])
               /\ (m["prevote"] \/ VotedFor_tmp[n] \in {None, m["from"]})
               /\ logOk
               /\ (m["prevote"] => ~leaderPresent)
         IN
         /\ Net' = (Net \ {m}) \cup {[
              id |-> MsgId + 1,
              type |-> "RequestVoteResp",
              from |-> n, to |-> m["from"],
              term |-> (IF m["prevote"] THEN Term[n] ELSE Term'[n]),
              prevote |-> m["prevote"],
              candidate |-> m["candidate"],
              lastLogIndex |-> 0,
              lastLogTerm |-> 0,
              voteGranted |-> canGrant,
              prevLogIndex |-> 0,
              prevLogTerm |-> 0,
              entries |-> <<>>,
              leaderCommit |-> 0,
              success |-> FALSE,
              currentIndex |-> 0,
              isHeartbeat |-> FALSE ]}
         /\ MsgId' = MsgId + 1
         /\ VotedFor' =
              IF ~m["prevote"] /\ canGrant
              THEN [VotedFor_tmp EXCEPT ![n] = m["from"]]
              ELSE VotedFor_tmp
         /\ UNCHANGED <<Members,Voters,LeaderOf,Log,CommitIndex,LastApplied,SnapshotIndex,SnapshotTerm,NextIndex,MatchIndex,ElectionElapsed,ElectionTimeoutRand,HBElapsed,Votes,PreVotes>>

RecvRequestVoteResponse ==
    \E m \in Net:
      /\ m["type"] = "RequestVoteResp"
      /\ \E n \in NODES: m["to"] = n
      /\ IF ~m["prevote"] /\ m["term"] > Term[n] THEN
           /\ Term' = [Term EXCEPT ![n] = m["term"]]
           /\ State' = [State EXCEPT ![n] = "FOLLOWER"]
           /\ VotedFor' = [VotedFor EXCEPT ![n] = None]
         ELSE
           /\ UNCHANGED <<Term,State,VotedFor>>
      /\ IF m["prevote"] /\ State[n] = "PRECANDIDATE" /\ m["term"] = Term[n] + 1 /\ m["voteGranted"] THEN
           /\ PreVotes' = [PreVotes EXCEPT ![n] = PreVotes[n] \cup {m["from"]}]
         ELSE
           /\ UNCHANGED PreVotes
      /\ IF ~m["prevote"] /\ State[n] = "CANDIDATE" /\ m["term"] = Term[n] /\ m["voteGranted"] THEN
           /\ Votes' = [Votes EXCEPT ![n] = Votes[n] \cup {m["from"]}]
         ELSE
           /\ UNCHANGED Votes
      /\ Net' = Net \ {m}
      /\ UNCHANGED <<Members,Voters,LeaderOf,Log,CommitIndex,LastApplied,SnapshotIndex,SnapshotTerm,NextIndex,MatchIndex,ElectionElapsed,ElectionTimeoutRand,HBElapsed,MsgId>>

AddNode ==
    \E l \in NODES, x \in NODES:
      /\ State[l] = "LEADER"
      /\ x \notin Members
      /\ Log' = [Log EXCEPT ![l] = AppendEntriesOf(l, << [term |-> Term[l], type |-> "ADD_NODE", node |-> x] >>)]
      /\ UNCHANGED <<Members,Voters,State,Term,VotedFor,LeaderOf,CommitIndex,LastApplied,SnapshotIndex,SnapshotTerm,NextIndex,MatchIndex,ElectionElapsed,ElectionTimeoutRand,HBElapsed,Net,MsgId,Votes,PreVotes>>

RemoveNode ==
    \E l \in NODES, x \in Members:
      /\ State[l] = "LEADER"
      /\ x # l
      /\ Log' = [Log EXCEPT ![l] = AppendEntriesOf(l, << [term |-> Term[l], type |-> "REMOVE_NODE", node |-> x] >>)]
      /\ UNCHANGED <<Members,Voters,State,Term,VotedFor,LeaderOf,CommitIndex,LastApplied,SnapshotIndex,SnapshotTerm,NextIndex,MatchIndex,ElectionElapsed,ElectionTimeoutRand,HBElapsed,Net,MsgId,Votes,PreVotes>>

ApplyConfigChange ==
    \E n \in NODES:
      /\ LastApplied[n] < CommitIndex[n]
      /\ HasEntryAt(n, LastApplied[n] + 1)
      /\ LET e == Log[n][(LastApplied[n] + 1) - SnapshotIndex[n]] IN
         /\ Members' =
              IF e["type"] = "ADD_NODE" THEN Members \cup {e["node"]}
              ELSE IF e["type"] = "ADD_NONVOTING_NODE" THEN Members \cup {e["node"]}
              ELSE IF e["type"] = "REMOVE_NODE" THEN Members \ {e["node"]}
              ELSE Members
         /\ Voters' =
              IF e["type"] = "ADD_NODE" THEN Voters \cup {e["node"]}
              ELSE IF e["type"] = "ADD_NONVOTING_NODE" THEN Voters \ {e["node"]}
              ELSE IF e["type"] = "REMOVE_NODE" THEN Voters \ {e["node"]}
              ELSE Voters
         /\ LastApplied' = [LastApplied EXCEPT ![n] = LastApplied[n] + 1]
         /\ UNCHANGED <<State,Term,VotedFor,LeaderOf,Log,CommitIndex,SnapshotIndex,SnapshotTerm,NextIndex,MatchIndex,ElectionElapsed,ElectionTimeoutRand,HBElapsed,Net,MsgId,Votes,PreVotes>>

SnapshotBegin ==
    \E n \in NODES:
      /\ LastApplied[n] > SnapshotIndex[n]
      /\ CommitIndex[n] >= LastApplied[n]
      /\ UNCHANGED <<Members,Voters,State,Term,VotedFor,LeaderOf,Log,CommitIndex,LastApplied,SnapshotIndex,SnapshotTerm,NextIndex,MatchIndex,ElectionElapsed,ElectionTimeoutRand,HBElapsed,Net,MsgId,Votes,PreVotes>>

SnapshotEnd ==
    \E n \in NODES:
      /\ LastApplied[n] >= SnapshotIndex[n]
      /\ LET newBase == LastApplied[n] IN
         /\ SnapshotTerm' = [SnapshotTerm EXCEPT ![n] = TermAt(n, newBase)]
         /\ SnapshotIndex' = [SnapshotIndex EXCEPT ![n] = newBase]
         /\ Log' =
              [Log EXCEPT
                  ![n] =
                      IF newBase < LastIndex(n)
                      THEN SubSeq(Log[n], (newBase - SnapshotIndex[n]) + 1, Len(Log[n]))
                      ELSE <<>> ]
      /\ UNCHANGED <<Members,Voters,State,Term,VotedFor,LeaderOf,CommitIndex,LastApplied,NextIndex,MatchIndex,ElectionElapsed,ElectionTimeoutRand,HBElapsed,Net,MsgId,Votes,PreVotes>>

vars == <<Members,Voters,State,Term,VotedFor,LeaderOf,Log,CommitIndex,LastApplied,SnapshotIndex,SnapshotTerm,NextIndex,MatchIndex,ElectionElapsed,ElectionTimeoutRand,HBElapsed,Net,MsgId,Votes,PreVotes>>

Next ==
    \/ \E n \in NODES: BecomeFollower(n)
    \/ \E n \in NODES: BecomePreCandidate(n)
    \/ \E n \in NODES: BecomeCandidate(n)
    \/ \E n \in NODES: BecomeLeader(n)
    \/ \E n \in NODES: ElectionStart(n)
    \/ ElectionTimeout
    \/ PeriodicElectionTimeout
    \/ SendHeartbeat
    \/ PeriodicHeartbeat
    \/ SendAppendEntries
    \/ RecvAppendEntries
    \/ RecvAppendEntriesResponse
    \/ RecvRequestVote
    \/ RecvRequestVoteResponse
    \/ LogDelete
    \/ LogAppend
    \/ LogCommit
    \/ AddNode
    \/ RemoveNode
    \/ ApplyConfigChange
    \/ SnapshotBegin
    \/ SnapshotEnd

Spec == Init /\ [][Next]_vars

====