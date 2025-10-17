---- MODULE redisraft ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS
    AllNodes,
    InitMembers,
    InitVoters,
    None,
    ELECTION_TIMEOUT,
    HEARTBEAT_INTERVAL

(*
State variables
*)
VARIABLES
    state,
    currentTerm,
    votedFor,
    log,
    commitIndex,
    lastApplied,
    snapshotIdx,
    snapshotTerm,
    snapshotInProgress,
    nextSnapshotLastIdx,
    nextSnapshotLastTerm,
    leaderId,
    timer,
    eTimeoutRand,
    hbTimer,
    Members,
    Voters,
    NextIndex,
    MatchIndex,
    Msgs,
    nextMsgId,
    PreVotesGranted,
    VotesGranted

States == {"FOLLOWER","PRECANDIDATE","CANDIDATE","LEADER"}
EntryTypes == {"no_op","cmd","add","add_nonvoting","remove"}

Vars == << state, currentTerm, votedFor, log, commitIndex, lastApplied, snapshotIdx, snapshotTerm, snapshotInProgress, nextSnapshotLastIdx, nextSnapshotLastTerm, leaderId, timer, eTimeoutRand, hbTimer, Members, Voters, NextIndex, MatchIndex, Msgs, nextMsgId, PreVotesGranted, VotesGranted >>

ElectionTimeoutRange == { ELECTION_TIMEOUT + d : d \in 0..ELECTION_TIMEOUT }
MajorityCard(S) == (Cardinality(S) \div 2) + 1

LastIndex(n) == snapshotIdx[n] + Len(log[n])
LastTerm(n) ==
    IF Len(log[n]) = 0 THEN snapshotTerm[n]
    ELSE log[n][Len(log[n])].term

Pos(n,i) == i - snapshotIdx[n]
HasPos(n,i) == /\ i > snapshotIdx[n] /\ i <= LastIndex(n)
TermAt(n,i) ==
    IF i = snapshotIdx[n] THEN snapshotTerm[n]
    ELSE IF HasPos(n,i) THEN log[n][Pos(n,i)].term
    ELSE 0

IsUpToDate(cTerm, cIdx, n) ==
    \/ cTerm > LastTerm(n)
    \/ /\ cTerm = LastTerm(n)
       /\ cIdx >= LastIndex(n)

IsVoting(n,x) == x \in Voters[n]
IsMember(n,x) == x \in Members[n]

UncommittedVotingCfgChange(n) ==
    \E i \in (commitIndex[n]+1)..LastIndex(n) :
        log[n][Pos(n,i)].type \in {"add","remove"}

MessageTypes == {
    "RequestVote","RequestVoteResponse",
    "AppendEntries","AppendEntriesResponse"
}

IsAE(m) == m.type = "AppendEntries"
IsAER(m) == m.type = "AppendEntriesResponse"
IsRV(m) == m.type = "RequestVote"
IsRVR(m) == m.type = "RequestVoteResponse"

Init ==
    /\ state \in [AllNodes -> States]
    /\ state = [n \in AllNodes |-> "FOLLOWER"]
    /\ currentTerm \in [AllNodes -> Nat]
    /\ currentTerm = [n \in AllNodes |-> 0]
    /\ votedFor \in [AllNodes -> (AllNodes \cup {None})]
    /\ votedFor = [n \in AllNodes |-> None]
    /\ log \in [AllNodes -> Seq([term: Nat, type: EntryTypes, node: AllNodes])]
    /\ log = [n \in AllNodes |-> << >>]
    /\ commitIndex \in [AllNodes -> Nat]
    /\ commitIndex = [n \in AllNodes |-> 0]
    /\ lastApplied \in [AllNodes -> Nat]
    /\ lastApplied = [n \in AllNodes |-> 0]
    /\ snapshotIdx \in [AllNodes -> Nat]
    /\ snapshotIdx = [n \in AllNodes |-> 0]
    /\ snapshotTerm \in [AllNodes -> Nat]
    /\ snapshotTerm = [n \in AllNodes |-> 0]
    /\ snapshotInProgress \in [AllNodes -> BOOLEAN]
    /\ snapshotInProgress = [n \in AllNodes |-> FALSE]
    /\ nextSnapshotLastIdx \in [AllNodes -> Nat]
    /\ nextSnapshotLastIdx = [n \in AllNodes |-> 0]
    /\ nextSnapshotLastTerm \in [AllNodes -> Nat]
    /\ nextSnapshotLastTerm = [n \in AllNodes |-> 0]
    /\ leaderId \in [AllNodes -> (AllNodes \cup {None})]
    /\ leaderId = [n \in AllNodes |-> None]
    /\ timer \in [AllNodes -> Nat]
    /\ timer = [n \in AllNodes |-> 0]
    /\ eTimeoutRand \in [AllNodes -> Nat]
    /\ \A n \in AllNodes : eTimeoutRand[n] \in ElectionTimeoutRange
    /\ hbTimer \in [AllNodes -> Nat]
    /\ hbTimer = [n \in AllNodes |-> 0]
    /\ Members \in [AllNodes -> SUBSET AllNodes]
    /\ Members = [n \in AllNodes |-> InitMembers]
    /\ Voters \in [AllNodes -> SUBSET AllNodes]
    /\ Voters = [n \in AllNodes |-> InitVoters]
    /\ NextIndex \in [AllNodes -> [AllNodes -> Nat]]
    /\ NextIndex = [l \in AllNodes |-> [m \in AllNodes |-> 1]]
    /\ MatchIndex \in [AllNodes -> [AllNodes -> Nat]]
    /\ MatchIndex = [l \in AllNodes |-> [m \in AllNodes |-> 0]]
    /\ Msgs \subseteq
        { [id: Nat, type: MessageTypes, from: AllNodes, to: AllNodes,
           term: Nat,
           prevote: BOOLEAN,
           requestTerm: Nat,
           candidate: AllNodes,
           lastIndex: Nat, lastTerm: Nat,
           leader: AllNodes,
           prevLogIndex: Nat, prevLogTerm: Nat,
           entries: Seq([term: Nat, type: EntryTypes, node: AllNodes]),
           leaderCommit: Nat,
           success: BOOLEAN,
           matchIndex: Nat] }
    /\ Msgs = {}
    /\ nextMsgId \in Nat
    /\ nextMsgId = 1
    /\ PreVotesGranted \in [AllNodes -> SUBSET AllNodes]
    /\ PreVotesGranted = [n \in AllNodes |-> {}]
    /\ VotesGranted \in [AllNodes -> SUBSET AllNodes]
    /\ VotesGranted = [n \in AllNodes |-> {}]

ResetElectionTimer(n) ==
    /\ timer' = [timer EXCEPT ![n] = 0]
    /\ eTimeoutRand' = [eTimeoutRand EXCEPT ![n] \in ElectionTimeoutRange]
    /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, lastApplied, snapshotIdx, snapshotTerm, snapshotInProgress, nextSnapshotLastIdx, nextSnapshotLastTerm, leaderId, hbTimer, Members, Voters, NextIndex, MatchIndex, Msgs, nextMsgId, PreVotesGranted, VotesGranted >>

BecomeFollower ==
    \E n \in AllNodes :
    /\ state[n] # "FOLLOWER"
    /\ state' = [state EXCEPT ![n] = "FOLLOWER"]
    /\ leaderId' = [leaderId EXCEPT ![n] = None]
    /\ votedFor' = votedFor
    /\ currentTerm' = currentTerm
    /\ PreVotesGranted' = [PreVotesGranted EXCEPT ![n] = {}]
    /\ VotesGranted' = [VotesGranted EXCEPT ![n] = {}]
    /\ timer' = [timer EXCEPT ![n] = 0]
    /\ eTimeoutRand' = [eTimeoutRand EXCEPT ![n] \in ElectionTimeoutRange]
    /\ UNCHANGED << log, commitIndex, lastApplied, snapshotIdx, snapshotTerm, snapshotInProgress, nextSnapshotLastIdx, nextSnapshotLastTerm, hbTimer, Members, Voters, NextIndex, MatchIndex, Msgs, nextMsgId >>

BecomePreCandidate ==
    \E n \in AllNodes :
    /\ state[n] # "LEADER"
    /\ state[n] # "PRECANDIDATE"
    /\ state' = [state EXCEPT ![n] = "PRECANDIDATE"]
    /\ PreVotesGranted' = [PreVotesGranted EXCEPT ![n] = {}]
    /\ VotesGranted' = [VotesGranted EXCEPT ![n] = {}]
    /\ hbTimer' = hbTimer
    /\ leaderId' = [leaderId EXCEPT ![n] = None]
    /\ votedFor' = votedFor
    /\ currentTerm' = currentTerm
    /\ timer' = [timer EXCEPT ![n] = 0]
    /\ eTimeoutRand' = [eTimeoutRand EXCEPT ![n] \in ElectionTimeoutRange]
    /\ Msgs' =
        LET LIdx == LastIndex(n) IN
        LET LTerm == LastTerm(n) IN
        Msgs \cup
        { [ id |-> nextMsgId + i,
            type |-> "RequestVote",
            from |-> n, to |-> m, term |-> currentTerm[n] + 1,
            prevote |-> TRUE, requestTerm |-> currentTerm[n] + 1,
            candidate |-> n,
            lastIndex |-> LIdx, lastTerm |-> LTerm,
            leader |-> n, prevLogIndex |-> 0, prevLogTerm |-> 0,
            entries |-> << >>, leaderCommit |-> commitIndex[n],
            success |-> FALSE, matchIndex |-> 0 ]
          : m \in Voters[n] \cap Members[n] \setminus {n} \land
            i \in 1..Cardinality(Voters[n] \cap Members[n] \setminus {n}) }
    /\ nextMsgId' = nextMsgId + Cardinality(Voters[n] \cap Members[n] \setminus {n})
    /\ UNCHANGED << log, commitIndex, lastApplied, snapshotIdx, snapshotTerm, snapshotInProgress, nextSnapshotLastIdx, nextSnapshotLastTerm, Members, Voters, NextIndex, MatchIndex, state >>

BecomeCandidate ==
    \E n \in AllNodes :
    /\ state[n] = "PRECANDIDATE" \/ state[n] = "FOLLOWER"
    /\ state' = [state EXCEPT ![n] = "CANDIDATE"]
    /\ currentTerm' = [currentTerm EXCEPT ![n] = currentTerm[n] + 1]
    /\ votedFor' = [votedFor EXCEPT ![n] = n]
    /\ VotesGranted' = [VotesGranted EXCEPT ![n] = (IF n \in Voters[n] THEN {n} ELSE {})]
    /\ PreVotesGranted' = [PreVotesGranted EXCEPT ![n] = {}]
    /\ leaderId' = [leaderId EXCEPT ![n] = None]
    /\ timer' = [timer EXCEPT ![n] = 0]
    /\ eTimeoutRand' = [eTimeoutRand EXCEPT ![n] \in ElectionTimeoutRange]
    /\ hbTimer' = hbTimer
    /\ Msgs' =
        LET LIdx == LastIndex(n) IN
        LET LTerm == LastTerm(n) IN
        Msgs \cup
        { [ id |-> nextMsgId + i,
            type |-> "RequestVote",
            from |-> n, to |-> m, term |-> currentTerm[n] + 1,
            prevote |-> FALSE, requestTerm |-> currentTerm[n] + 1,
            candidate |-> n,
            lastIndex |-> LIdx, lastTerm |-> LTerm,
            leader |-> n, prevLogIndex |-> 0, prevLogTerm |-> 0,
            entries |-> << >>, leaderCommit |-> commitIndex[n],
            success |-> FALSE, matchIndex |-> 0 ]
          : m \in Voters[n] \cap Members[n] \setminus {n} \land
            i \in 1..Cardinality(Voters[n] \cap Members[n] \setminus {n}) }
    /\ nextMsgId' = nextMsgId + Cardinality(Voters[n] \cap Members[n] \setminus {n})
    /\ UNCHANGED << log, commitIndex, lastApplied, snapshotIdx, snapshotTerm, snapshotInProgress, nextSnapshotLastIdx, nextSnapshotLastTerm, Members, Voters, NextIndex, MatchIndex >>

BecomeLeader ==
    \E n \in AllNodes :
    /\ state[n] = "CANDIDATE"
    /\ state' = [state EXCEPT ![n] = "LEADER"]
    /\ leaderId' = [leaderId EXCEPT ![n] = n]
    /\ log' =
        [log EXCEPT
            ![n] = Append(log[n], [term |-> currentTerm[n], type |-> "no_op", node |-> n])]
    /\ commitIndex' =
        [commitIndex EXCEPT
            ![n] = IF Cardinality(Voters[n]) = 1 THEN LastIndex(n) + 1 ELSE @]
    /\ lastApplied' = lastApplied
    /\ NextIndex' =
        [NextIndex EXCEPT
            ![n] = [m \in AllNodes |-> (LastIndex(n) + 2)]]
    /\ MatchIndex' =
        [MatchIndex EXCEPT
            ![n] = [m \in AllNodes |-> IF m = n THEN LastIndex(n) + 1 ELSE 0]]
    /\ hbTimer' = [hbTimer EXCEPT ![n] = 0]
    /\ PreVotesGranted' = [PreVotesGranted EXCEPT ![n] = {}]
    /\ VotesGranted' = [VotesGranted EXCEPT ![n] = {}]
    /\ UNCHANGED << currentTerm, votedFor, snapshotIdx, snapshotTerm, snapshotInProgress, nextSnapshotLastIdx, nextSnapshotLastTerm, timer, eTimeoutRand, Members, Voters, Msgs, nextMsgId >>

ElectionStart ==
    \E n \in AllNodes :
    /\ state[n] # "LEADER"
    /\ timer[n] >= eTimeoutRand[n]
    /\ state' = [state EXCEPT ![n] = "PRECANDIDATE"]
    /\ PreVotesGranted' = [PreVotesGranted EXCEPT ![n] = {}]
    /\ VotesGranted' = [VotesGranted EXCEPT ![n] = {}]
    /\ leaderId' = [leaderId EXCEPT ![n] = None]
    /\ timer' = [timer EXCEPT ![n] = 0]
    /\ eTimeoutRand' = [eTimeoutRand EXCEPT ![n] \in ElectionTimeoutRange]
    /\ Msgs' =
        LET LIdx == LastIndex(n) IN
        LET LTerm == LastTerm(n) IN
        Msgs \cup
        { [ id |-> nextMsgId + i,
            type |-> "RequestVote",
            from |-> n, to |-> m, term |-> currentTerm[n] + 1,
            prevote |-> TRUE, requestTerm |-> currentTerm[n] + 1,
            candidate |-> n,
            lastIndex |-> LIdx, lastTerm |-> LTerm,
            leader |-> n, prevLogIndex |-> 0, prevLogTerm |-> 0,
            entries |-> << >>, leaderCommit |-> commitIndex[n],
            success |-> FALSE, matchIndex |-> 0 ]
          : m \in Voters[n] \cap Members[n] \setminus {n} \land
            i \in 1..Cardinality(Voters[n] \cap Members[n] \setminus {n}) }
    /\ nextMsgId' = nextMsgId + Cardinality(Voters[n] \cap Members[n] \setminus {n})
    /\ UNCHANGED << currentTerm, votedFor, log, commitIndex, lastApplied, snapshotIdx, snapshotTerm, snapshotInProgress, nextSnapshotLastIdx, nextSnapshotLastTerm, hbTimer, Members, Voters, NextIndex, MatchIndex >>

ElectionTimeout ==
    \E n \in AllNodes :
    /\ state[n] # "LEADER"
    /\ timer[n] < eTimeoutRand[n]
    /\ timer' = [timer EXCEPT ![n] = timer[n] + 1]
    /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, lastApplied, snapshotIdx, snapshotTerm, snapshotInProgress, nextSnapshotLastIdx, nextSnapshotLastTerm, leaderId, eTimeoutRand, hbTimer, Members, Voters, NextIndex, MatchIndex, Msgs, nextMsgId, PreVotesGranted, VotesGranted >>

PeriodicElectionTimeout == ElectionTimeout

SendAppendEntries ==
    \E l \in AllNodes :
    \E f \in (Members[l] \cap AllNodes) \setminus {l} :
    /\ state[l] = "LEADER"
    /\ LET next == NextIndex[l][f] IN
       /\ next >= 1
       /\ LET prevIdx == next - 1 IN
          LET prevTerm == TermAt(l, prevIdx) IN
          LET k == IF next <= LastIndex(l) + 1 THEN (LastIndex(l) - next + 1) ELSE 0 IN
          LET ents ==
              IF k = 0 THEN << >>
              ELSE SubSeq(log[l], Pos(l,next), Len(log[l])) IN
          /\ Msgs' =
                Msgs \cup {
                    [ id |-> nextMsgId,
                      type |-> "AppendEntries",
                      from |-> l, to |-> f,
                      term |-> currentTerm[l],
                      prevote |-> FALSE,
                      requestTerm |-> currentTerm[l],
                      candidate |-> l,
                      lastIndex |-> LastIndex(l), lastTerm |-> LastTerm(l),
                      leader |-> l,
                      prevLogIndex |-> prevIdx, prevLogTerm |-> prevTerm,
                      entries |-> ents,
                      leaderCommit |-> commitIndex[l],
                      success |-> FALSE, matchIndex |-> 0 ]
                }
          /\ nextMsgId' = nextMsgId + 1
          /\ NextIndex' = NextIndex
          /\ MatchIndex' = MatchIndex
    /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, lastApplied, snapshotIdx, snapshotTerm, snapshotInProgress, nextSnapshotLastIdx, nextSnapshotLastTerm, leaderId, timer, eTimeoutRand, hbTimer, Members, Voters, PreVotesGranted, VotesGranted >>

SendHeartbeat ==
    \E l \in AllNodes :
    \E f \in (Members[l] \cap AllNodes) \setminus {l} :
    /\ state[l] = "LEADER"
    /\ hbTimer[l] >= HEARTBEAT_INTERVAL
    /\ LET prevIdx == NextIndex[l][f] - 1 IN
       LET prevTerm == TermAt(l, prevIdx) IN
       /\ Msgs' =
            Msgs \cup {
                [ id |-> nextMsgId,
                  type |-> "AppendEntries",
                  from |-> l, to |-> f,
                  term |-> currentTerm[l],
                  prevote |-> FALSE,
                  requestTerm |-> currentTerm[l],
                  candidate |-> l,
                  lastIndex |-> LastIndex(l), lastTerm |-> LastTerm(l),
                  leader |-> l,
                  prevLogIndex |-> prevIdx, prevLogTerm |-> prevTerm,
                  entries |-> << >>,
                  leaderCommit |-> commitIndex[l],
                  success |-> FALSE, matchIndex |-> 0 ]
            }
    /\ nextMsgId' = nextMsgId + 1
    /\ hbTimer' = [hbTimer EXCEPT ![l] = 0]
    /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, lastApplied, snapshotIdx, snapshotTerm, snapshotInProgress, nextSnapshotLastIdx, nextSnapshotLastTerm, leaderId, timer, eTimeoutRand, Members, Voters, NextIndex, MatchIndex, PreVotesGranted, VotesGranted >>

PeriodicHeartbeat ==
    \E n \in AllNodes :
    /\ state[n] = "LEADER"
    /\ hbTimer' = [hbTimer EXCEPT ![n] = hbTimer[n] + 1]
    /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, lastApplied, snapshotIdx, snapshotTerm, snapshotInProgress, nextSnapshotLastIdx, nextSnapshotLastTerm, leaderId, timer, eTimeoutRand, Members, Voters, NextIndex, MatchIndex, Msgs, nextMsgId, PreVotesGranted, VotesGranted >>

RecvAppendEntries ==
    \E m \in Msgs :
    /\ IsAE(m)
    /\ LET r == m IN
       \E n \in AllNodes :
       /\ r.to = n
       /\ Msgs' = Msgs \ {r}
       /\ \/ r.term < currentTerm[n]
          \/ LET ct == currentTerm[n] IN
             LET ct' == (IF r.term > currentTerm[n] THEN r.term ELSE currentTerm[n]) IN
             /\ currentTerm' = [currentTerm EXCEPT ![n] = ct']
             /\ state' = [state EXCEPT ![n] = "FOLLOWER"]
             /\ leaderId' = [leaderId EXCEPT ![n] = r.leader]
             /\ timer' = [timer EXCEPT ![n] = 0]
             /\ eTimeoutRand' = eTimeoutRand
             /\ hbTimer' = hbTimer
             /\ LET ok ==
                    /\ r.prevLogIndex = snapshotIdx[n] => r.prevLogTerm = snapshotTerm[n]
                    /\ r.prevLogIndex > snapshotIdx[n] =>
                        /\ r.prevLogIndex <= LastIndex(n)
                        /\ TermAt(n, r.prevLogIndex) = r.prevLogTerm
                IN
                /\ IF ~ok THEN
                        /\ log' = log
                        /\ commitIndex' = commitIndex
                        /\ lastApplied' = lastApplied
                   ELSE
                        /\ log' =
                            [log EXCEPT
                                ![n] =
                                    LET keepLen ==
                                        IF r.prevLogIndex = snapshotIdx[n]
                                        THEN 0
                                        ELSE Pos(n,r.prevLogIndex)
                                    IN
                                    SubSeq(log[n],1,keepLen) \o r.entries]
                        /\ commitIndex' =
                            [commitIndex EXCEPT
                                ![n] = Min(r.leaderCommit, LastIndex(n) + Len(r.entries))]
                        /\ lastApplied' = lastApplied
             /\ snapshotIdx' = snapshotIdx
             /\ snapshotTerm' = snapshotTerm
             /\ snapshotInProgress' = snapshotInProgress
             /\ nextSnapshotLastIdx' = nextSnapshotLastIdx
             /\ nextSnapshotLastTerm' = nextSnapshotLastTerm
             /\ Members' = Members
             /\ Voters' = Voters
             /\ votedFor' = votedFor
             /\ NextIndex' = NextIndex
             /\ MatchIndex' = MatchIndex
             /\ PreVotesGranted' = PreVotesGranted
             /\ VotesGranted' = VotesGranted
    /\ UNCHANGED << nextMsgId >>

RecvAppendEntriesResponse ==
    \E m \in Msgs :
    /\ IsAER(m)
    /\ LET r == m IN
       \E l \in AllNodes :
       /\ r.to = l
       /\ Msgs' = Msgs \ {r}
       /\ \/ r.term > currentTerm[l]
          \/ /\ state[l] = "LEADER"
             /\ r.term = currentTerm[l]
             /\ LET f == r.from IN
                /\ IF r.success THEN
                      /\ MatchIndex' =
                         [MatchIndex EXCEPT ![l] = [MatchIndex[l] EXCEPT ![f] = r.matchIndex]]
                      /\ NextIndex' =
                         [NextIndex EXCEPT ![l] = [NextIndex[l] EXCEPT ![f] = r.matchIndex + 1]]
                   ELSE
                      /\ MatchIndex' = MatchIndex
                      /\ NextIndex' =
                         [NextIndex EXCEPT ![l] = [NextIndex[l] EXCEPT ![f] = Max(1, NextIndex[l][f] - 1)]]
             /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, lastApplied, snapshotIdx, snapshotTerm, snapshotInProgress, nextSnapshotLastIdx, nextSnapshotLastTerm, leaderId, timer, eTimeoutRand, hbTimer, Members, Voters, PreVotesGranted, VotesGranted, nextMsgId >>

RecvRequestVote ==
    \E m \in Msgs :
    /\ IsRV(m)
    /\ LET r == m IN
       \E n \in AllNodes :
       /\ r.to = n
       /\ Msgs' = Msgs \ {r} \cup {
            [ id |-> nextMsgId,
              type |-> "RequestVoteResponse",
              from |-> n, to |-> r.from,
              term |-> (IF r.prevote THEN currentTerm[n] ELSE Max(currentTerm[n], r.term)),
              prevote |-> r.prevote,
              requestTerm |-> r.requestTerm,
              candidate |-> r.candidate,
              lastIndex |-> LastIndex(n), lastTerm |-> LastTerm(n),
              leader |-> leaderId[n],
              prevLogIndex |-> 0, prevLogTerm |-> 0,
              entries |-> << >>,
              leaderCommit |-> commitIndex[n],
              success |-> (\* overloaded as voteGranted *) (LET up == IsUpToDate(r.lastTerm, r.lastIndex, n) IN
                           IF r.prevote THEN up
                           ELSE
                             /\ r.term >= currentTerm[n]
                             /\ up
                             /\ (votedFor[n] = None \/ votedFor[n] = r.candidate))
              ,
              matchIndex |-> 0 ] }
       /\ nextMsgId' = nextMsgId + 1
       /\ IF r.prevote THEN
             /\ currentTerm' = currentTerm
             /\ state' = state
             /\ votedFor' = votedFor
             /\ leaderId' = leaderId
             /\ timer' = timer
             /\ eTimeoutRand' = eTimeoutRand
          ELSE
             /\ currentTerm' =
                [currentTerm EXCEPT ![n] = Max(currentTerm[n], r.term)]
             /\ IF r.term > currentTerm[n] THEN
                    /\ state' = [state EXCEPT ![n] = "FOLLOWER"]
                    /\ votedFor' =
                        [votedFor EXCEPT ![n] =
                            IF IsUpToDate(r.lastTerm, r.lastIndex, n) THEN r.candidate ELSE @]
                    /\ leaderId' = [leaderId EXCEPT ![n] = None]
                    /\ timer' = [timer EXCEPT ![n] = 0]
                    /\ eTimeoutRand' = [eTimeoutRand EXCEPT ![n] \in ElectionTimeoutRange]
                ELSE
                    /\ state' = state
                    /\ votedFor' =
                        [votedFor EXCEPT ![n] =
                            IF /\ r.term = currentTerm[n]
                               /\ IsUpToDate(r.lastTerm, r.lastIndex, n)
                               /\ (votedFor[n] = None \/ votedFor[n] = r.candidate)
                            THEN r.candidate ELSE @]
                    /\ leaderId' = [leaderId EXCEPT ![n] = None]
                    /\ timer' = [timer EXCEPT ![n] = 0]
                    /\ eTimeoutRand' = eTimeoutRand
       /\ UNCHANGED << log, commitIndex, lastApplied, snapshotIdx, snapshotTerm, snapshotInProgress, nextSnapshotLastIdx, nextSnapshotLastTerm, hbTimer, Members, Voters, NextIndex, MatchIndex, PreVotesGranted, VotesGranted >>

RecvRequestVoteResponse ==
    \E m \in Msgs :
    /\ IsRVR(m)
    /\ LET r == m IN
       \E n \in AllNodes :
       /\ r.to = n
       /\ Msgs' = Msgs \ {r}
       /\ IF r.prevote THEN
             /\ IF /\ state[n] = "PRECANDIDATE"
                   /\ r.requestTerm = currentTerm[n] + 1
                THEN
                    /\ PreVotesGranted' =
                        [PreVotesGranted EXCEPT
                            ![n] = PreVotesGranted[n] \cup {r.from}]
                    /\ IF Cardinality((PreVotesGranted[n] \cup {r.from}) \cap Voters[n]) >= MajorityCard(Voters[n])
                       THEN
                         /\ state' = [state EXCEPT ![n] = "CANDIDATE"]
                         /\ currentTerm' = [currentTerm EXCEPT ![n] = currentTerm[n] + 1]
                         /\ votedFor' = [votedFor EXCEPT ![n] = n]
                         /\ VotesGranted' = [VotesGranted EXCEPT ![n] = (IF n \in Voters[n] THEN {n} ELSE {})]
                         /\ PreVotesGranted' = [PreVotesGranted EXCEPT ![n] = {}]
                         /\ leaderId' = [leaderId EXCEPT ![n] = None]
                         /\ timer' = [timer EXCEPT ![n] = 0]
                         /\ eTimeoutRand' = [eTimeoutRand EXCEPT ![n] \in ElectionTimeoutRange]
                         /\ hbTimer' = hbTimer
                         /\ Msgs'' =
                             LET LIdx == LastIndex(n) IN
                             LET LTerm == LastTerm(n) IN
                             {
                               [ id |-> nextMsgId + i,
                                 type |-> "RequestVote",
                                 from |-> n, to |-> p, term |-> currentTerm[n] + 1,
                                 prevote |-> FALSE, requestTerm |-> currentTerm[n] + 1,
                                 candidate |-> n,
                                 lastIndex |-> LIdx, lastTerm |-> LTerm,
                                 leader |-> n, prevLogIndex |-> 0, prevLogTerm |-> 0,
                                 entries |-> << >>, leaderCommit |-> commitIndex[n],
                                 success |-> FALSE, matchIndex |-> 0 ]
                               : p \in Voters[n] \cap Members[n] \setminus {n}
                                 \land i \in 1..Cardinality(Voters[n] \cap Members[n] \setminus {n})
                             }
                         /\ Msgs' = Msgs' \cup Msgs''
                         /\ nextMsgId' = nextMsgId + Cardinality(Voters[n] \cap Members[n] \setminus {n})
                       ELSE
                         /\ state' = state
                         /\ currentTerm' = currentTerm
                         /\ votedFor' = votedFor
                         /\ VotesGranted' = VotesGranted
                         /\ leaderId' = leaderId
                         /\ timer' = timer
                         /\ eTimeoutRand' = eTimeoutRand
                         /\ hbTimer' = hbTimer
                         /\ nextMsgId' = nextMsgId
                ELSE
                    /\ state' = state
                    /\ currentTerm' = currentTerm
                    /\ votedFor' = votedFor
                    /\ PreVotesGranted' = PreVotesGranted
                    /\ VotesGranted' = VotesGranted
                    /\ leaderId' = leaderId
                    /\ timer' = timer
                    /\ eTimeoutRand' = eTimeoutRand
                    /\ hbTimer' = hbTimer
                    /\ nextMsgId' = nextMsgId
          ELSE
             /\ IF /\ state[n] = "CANDIDATE"
                   /\ r.requestTerm = currentTerm[n]
                   /\ r.term = currentTerm[n]
                THEN
                    /\ VotesGranted' =
                        [VotesGranted EXCEPT
                            ![n] = IF r.success THEN VotesGranted[n] \cup {r.from} ELSE @]
                    /\ IF r.success /\ Cardinality((VotesGranted[n] \cup {r.from}) \cap Voters[n]) >= MajorityCard(Voters[n])
                       THEN
                         /\ state' = [state EXCEPT ![n] = "LEADER"]
                         /\ leaderId' = [leaderId EXCEPT ![n] = n]
                         /\ log' =
                             [log EXCEPT
                                ![n] = Append(log[n], [term |-> currentTerm[n], type |-> "no_op", node |-> n])]
                         /\ commitIndex' =
                             [commitIndex EXCEPT
                                ![n] = IF Cardinality(Voters[n]) = 1 THEN LastIndex(n) + 1 ELSE @]
                         /\ lastApplied' = lastApplied
                         /\ NextIndex' =
                             [NextIndex EXCEPT ![n] = [m \in AllNodes |-> LastIndex(n) + 2]]
                         /\ MatchIndex' =
                             [MatchIndex EXCEPT ![n] = [m \in AllNodes |-> IF m = n THEN LastIndex(n) + 1 ELSE 0]]
                         /\ hbTimer' = [hbTimer EXCEPT ![n] = 0]
                         /\ PreVotesGranted' = [PreVotesGranted EXCEPT ![n] = {}]
                         /\ nextMsgId' = nextMsgId
                       ELSE
                         /\ state' = state
                         /\ leaderId' = leaderId
                         /\ log' = log
                         /\ commitIndex' = commitIndex
                         /\ lastApplied' = lastApplied
                         /\ NextIndex' = NextIndex
                         /\ MatchIndex' = MatchIndex
                         /\ hbTimer' = hbTimer
                         /\ PreVotesGranted' = PreVotesGranted
                         /\ nextMsgId' = nextMsgId
                ELSE
                    /\ state' = state
                    /\ currentTerm' = IF r.term > currentTerm[n] THEN [currentTerm EXCEPT ![n] = r.term] ELSE currentTerm
                    /\ votedFor' = votedFor
                    /\ PreVotesGranted' = PreVotesGranted
                    /\ VotesGranted' = VotesGranted
                    /\ leaderId' = leaderId
                    /\ timer' = timer
                    /\ eTimeoutRand' = eTimeoutRand
                    /\ hbTimer' = hbTimer
                    /\ nextMsgId' = nextMsgId
       /\ UNCHANGED << snapshotIdx, snapshotTerm, snapshotInProgress, nextSnapshotLastIdx, nextSnapshotLastTerm, Members, Voters, Msgs >>

LogAppend ==
    \E n \in AllNodes :
    /\ state[n] = "LEADER"
    /\ LET t \in EntryTypes IN
       LET e == [term |-> currentTerm[n], type |-> t, node |-> CHOOSE x \in AllNodes : TRUE] IN
       /\ (t \in {"add","remove"} => ~UncommittedVotingCfgChange(n))
       /\ log' = [log EXCEPT ![n] = Append(log[n], e)]
       /\ UNCHANGED << state, currentTerm, votedFor, commitIndex, lastApplied, snapshotIdx, snapshotTerm, snapshotInProgress, nextSnapshotLastIdx, nextSnapshotLastTerm, leaderId, timer, eTimeoutRand, hbTimer, Members, Voters, NextIndex, MatchIndex, Msgs, nextMsgId, PreVotesGranted, VotesGranted >>

LogDelete(n, idx) ==
    /\ HasPos(n, idx)
    /\ log' = [log EXCEPT ![n] = SubSeq(log[n], 1, Pos(n,idx))]
    /\ UNCHANGED << state, currentTerm, votedFor, commitIndex, lastApplied, snapshotIdx, snapshotTerm, snapshotInProgress, nextSnapshotLastIdx, nextSnapshotLastTerm, leaderId, timer, eTimeoutRand, hbTimer, Members, Voters, NextIndex, MatchIndex, Msgs, nextMsgId, PreVotesGranted, VotesGranted >>

LogCommit ==
    \E l \in AllNodes :
    /\ state[l] = "LEADER"
    /\ \E i \in (commitIndex[l]+1)..(LastIndex(l)) :
        /\ LET voters == Voters[l] IN
           LET count == Cardinality({ m \in voters : MatchIndex[l][m] >= i } \cup (IF l \in voters THEN {l} ELSE {})) IN
           /\ count >= MajorityCard(voters)
           /\ TermAt(l,i) = currentTerm[l]
    /\ commitIndex' =
        [commitIndex EXCEPT ![l] = CHOOSE j \in (commitIndex[l]+1)..LastIndex(l) :
            /\ TermAt(l,j) = currentTerm[l]
            /\ Cardinality({ m \in Voters[l] : MatchIndex[l][m] >= j } \cup (IF l \in Voters[l] THEN {l} ELSE {})) >= MajorityCard(Voters[l]) ]
    /\ UNCHANGED << state, currentTerm, votedFor, log, lastApplied, snapshotIdx, snapshotTerm, snapshotInProgress, nextSnapshotLastIdx, nextSnapshotLastTerm, leaderId, timer, eTimeoutRand, hbTimer, Members, Voters, NextIndex, MatchIndex, Msgs, nextMsgId, PreVotesGranted, VotesGranted >>

ApplyConfigChange ==
    \E n \in AllNodes :
    /\ lastApplied[n] < commitIndex[n]
    /\ LET i == lastApplied[n] + 1 IN
       LET e == log[n][Pos(n,i)] IN
       /\ e.type \in {"add", "add_nonvoting", "remove"}
       /\ lastApplied' = [lastApplied EXCEPT ![n] = i]
       /\ Members' =
            [Members EXCEPT
                ![n] =
                  IF e.type = "remove" THEN Members[n] \ {e.node}
                  ELSE Members[n] \cup {e.node}]
       /\ Voters' =
            [Voters EXCEPT
                ![n] =
                  IF e.type = "add" THEN Voters[n] \cup {e.node}
                  ELSE IF e.type = "remove" THEN Voters[n] \ {e.node}
                  ELSE Voters[n]]
       /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, snapshotIdx, snapshotTerm, snapshotInProgress, nextSnapshotLastIdx, nextSnapshotLastTerm, leaderId, timer, eTimeoutRand, hbTimer, NextIndex, MatchIndex, Msgs, nextMsgId, PreVotesGranted, VotesGranted >>

AddNode ==
    \E n \in AllNodes :
    /\ lastApplied[n] < commitIndex[n]
    /\ LET i == lastApplied[n] + 1 IN
       LET e == log[n][Pos(n,i)] IN
       /\ e.type = "add"
       /\ lastApplied' = [lastApplied EXCEPT ![n] = i]
       /\ Members' = [Members EXCEPT ![n] = Members[n] \cup {e.node}]
       /\ Voters' = [Voters EXCEPT ![n] = Voters[n] \cup {e.node}]
       /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, snapshotIdx, snapshotTerm, snapshotInProgress, nextSnapshotLastIdx, nextSnapshotLastTerm, leaderId, timer, eTimeoutRand, hbTimer, NextIndex, MatchIndex, Msgs, nextMsgId, PreVotesGranted, VotesGranted >>

RemoveNode ==
    \E n \in AllNodes :
    /\ lastApplied[n] < commitIndex[n]
    /\ LET i == lastApplied[n] + 1 IN
       LET e == log[n][Pos(n,i)] IN
       /\ e.type = "remove"
       /\ lastApplied' = [lastApplied EXCEPT ![n] = i]
       /\ Members' = [Members EXCEPT ![n] = Members[n] \ {e.node}]
       /\ Voters' = [Voters EXCEPT ![n] = Voters[n] \ {e.node}]
       /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, snapshotIdx, snapshotTerm, snapshotInProgress, nextSnapshotLastIdx, nextSnapshotLastTerm, leaderId, timer, eTimeoutRand, hbTimer, NextIndex, MatchIndex, Msgs, nextMsgId, PreVotesGranted, VotesGranted >>

ApplyEntries ==
    \E n \in AllNodes :
    /\ lastApplied[n] < commitIndex[n]
    /\ LET i == lastApplied[n] + 1 IN
       LET e == log[n][Pos(n,i)] IN
       /\ e.type \notin {"add","add_nonvoting","remove"}
       /\ lastApplied' = [lastApplied EXCEPT ![n] = i]
       /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, snapshotIdx, snapshotTerm, snapshotInProgress, nextSnapshotLastIdx, nextSnapshotLastTerm, leaderId, timer, eTimeoutRand, hbTimer, Members, Voters, NextIndex, MatchIndex, Msgs, nextMsgId, PreVotesGranted, VotesGranted >>

SnapshotBegin ==
    \E n \in AllNodes :
    /\ ~snapshotInProgress[n]
    /\ lastApplied[n] > snapshotIdx[n]
    /\ snapshotInProgress' = [snapshotInProgress EXCEPT ![n] = TRUE]
    /\ nextSnapshotLastIdx' = [nextSnapshotLastIdx EXCEPT ![n] = lastApplied[n]]
    /\ nextSnapshotLastTerm' = [nextSnapshotLastTerm EXCEPT ![n] = TermAt(n,lastApplied[n])]
    /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, lastApplied, snapshotIdx, snapshotTerm, leaderId, timer, eTimeoutRand, hbTimer, Members, Voters, NextIndex, MatchIndex, Msgs, nextMsgId, PreVotesGranted, VotesGranted >>

SnapshotEnd ==
    \E n \in AllNodes :
    /\ snapshotInProgress[n]
    /\ nextSnapshotLastIdx[n] >= snapshotIdx[n]
    /\ snapshotIdx' = [snapshotIdx EXCEPT ![n] = nextSnapshotLastIdx[n]]
    /\ snapshotTerm' = [snapshotTerm EXCEPT ![n] = nextSnapshotLastTerm[n]]
    /\ log' =
        [log EXCEPT
            ![n] =
                IF nextSnapshotLastIdx[n] = snapshotIdx[n]
                THEN log[n]
                ELSE SubSeq(log[n], Pos(n, nextSnapshotLastIdx[n]) + 1, Len(log[n]))]
    /\ snapshotInProgress' = [snapshotInProgress EXCEPT ![n] = FALSE]
    /\ UNCHANGED << state, currentTerm, votedFor, commitIndex, lastApplied, nextSnapshotLastIdx, nextSnapshotLastTerm, leaderId, timer, eTimeoutRand, hbTimer, Members, Voters, NextIndex, MatchIndex, Msgs, nextMsgId, PreVotesGranted, VotesGranted >>

Next ==
    \/ PeriodicElectionTimeout
    \/ ElectionTimeout
    \/ ElectionStart
    \/ BecomePreCandidate
    \/ BecomeCandidate
    \/ BecomeFollower
    \/ BecomeLeader
    \/ SendAppendEntries
    \/ SendHeartbeat
    \/ PeriodicHeartbeat
    \/ RecvAppendEntries
    \/ RecvAppendEntriesResponse
    \/ RecvRequestVote
    \/ RecvRequestVoteResponse
    \/ LogAppend
    \/ LogCommit
    \/ ApplyEntries
    \/ ApplyConfigChange
    \/ AddNode
    \/ RemoveNode
    \/ SnapshotBegin
    \/ SnapshotEnd

Spec == Init /\ [][Next]_Vars

====