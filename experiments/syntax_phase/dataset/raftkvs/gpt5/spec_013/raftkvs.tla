---- MODULE raftkvs ----
EXTENDS TLC, Sequences, Naturals, FiniteSets

CONSTANTS
    NumServers,
    NumClients,
    AllStrings

Server == 1..NumServers
Client == (NumServers + 1)..(NumServers + NumClients)
Node == Server \cup Client

Key == AllStrings
Value == AllStrings
Nil == 0

StateFollower == "follower"
StateCandidate == "candidate"
StateLeader == "leader"

PutT == "put"
GetT == "get"

LeaderTimeoutT == "LeaderTimeout"
RequestVoteRequestT == "rvq"
RequestVoteResponseT == "rvp"
AppendEntriesRequestT == "apq"
AppendEntriesResponseT == "app"
ClientPutRequestT == "cpq"
ClientPutResponseT == "cpp"
ClientGetRequestT == "cgq"
ClientGetResponseT == "cgp"

IsQuorum(S) == 2 * Cardinality(S) > NumServers

LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)].term

LogUpToDate(mlastLogTerm, mlastLogIndex, xlog) ==
    \/ mlastLogTerm > LastTerm(xlog)
    \/ /\ mlastLogTerm = LastTerm(xlog)
       /\ mlastLogIndex >= Len(xlog)

FollowerLogOK(mprevLogIndex, mprevLogTerm, xlog) ==
    \/ mprevLogIndex = 0
    \/ /\ mprevLogIndex > 0
       /\ mprevLogIndex <= Len(xlog)
       /\ xlog[mprevLogIndex].term = mprevLogTerm

RemoveAt1(s, k) ==
    SubSeq(s, 1, k - 1) \o SubSeq(s, k + 1, Len(s))

EntriesFrom(xlog, start) ==
    IF start <= Len(xlog) THEN SubSeq(xlog, start, Len(xlog)) ELSE << >>

MaxNat(S) == CHOOSE m \in S : \A x \in S : x <= m

ApplyEntry(entry, xsm, xdom) ==
    IF entry.cmd.type = PutT THEN
        << [ xsm EXCEPT ![entry.cmd.key] = entry.cmd.value ],
           xdom \cup { entry.cmd.key } >>
    ELSE
        << xsm, xdom >>

Message == [
    mtype: {RequestVoteRequestT, RequestVoteResponseT,
            AppendEntriesRequestT, AppendEntriesResponseT,
            ClientPutRequestT, ClientPutResponseT,
            ClientGetRequestT, ClientGetResponseT},
    mterm: Nat,
    msource: Node,
    mdest: Node,
    mlastLogIndex: Nat,
    mlastLogTerm: Nat,
    mvoteGranted: BOOLEAN,
    mprevLogIndex: Nat,
    mprevLogTerm: Nat,
    mentries: Seq([term: Nat, cmd: [type: {PutT, GetT}, key: Key, value: Value, idx: Nat], client: Client]),
    mcommitIndex: Nat,
    msuccess: BOOLEAN,
    mmatchIndex: Nat,
    mcmd: [type: {PutT, GetT}, key: Key, value: Value, idx: Nat],
    mleaderHint: Server \cup {Nil},
    mresponse: [idx: Nat, key: Key, value: Value, ok: BOOLEAN]
]

VARIABLES
    state,
    currentTerm,
    votedFor,
    leader,
    log,
    commitIndex,
    lastApplied,
    nextIndex,
    matchIndex,
    votesResponded,
    votesGranted,
    sm,
    smDomain,
    Timer,
    Net,
    SrvEnabled,
    cliLeader,
    cliReq,
    cliReqIdx,
    cliTimeout

vars == << state, currentTerm, votedFor, leader, log, commitIndex, lastApplied,
           nextIndex, matchIndex, votesResponded, votesGranted, sm, smDomain,
           Timer, Net, SrvEnabled, cliLeader, cliReq, cliReqIdx, cliTimeout >>

AgreeSet(i) ==
    { n \in 0..Len(log[i]) :
        IsQuorum({ k \in Server : (k = i) \/ (matchIndex[i][k] >= n) })
    }

FindMaxAgreeIndex(i) ==
    IF AgreeSet(i) = {} THEN 0 ELSE MaxNat(AgreeSet(i))

Init ==
    /\ state = [i \in Server |-> StateFollower]
    /\ currentTerm = [i \in Server |-> 0]
    /\ votedFor = [i \in Server |-> Nil]
    /\ leader = [i \in Server |-> Nil]
    /\ log = [i \in Server |-> << >>]
    /\ commitIndex = [i \in Server |-> 0]
    /\ lastApplied = [i \in Server |-> 0]
    /\ nextIndex = [i \in Server |-> [j \in Server |-> 1]]
    /\ matchIndex = [i \in Server |-> [j \in Server |-> 0]]
    /\ votesResponded = [i \in Server |-> {}]
    /\ votesGranted = [i \in Server |-> {}]
    /\ sm = [i \in Server |-> [k \in Key |-> Nil]]
    /\ smDomain = [i \in Server |-> {}]
    /\ Timer = [i \in Server |-> FALSE]
    /\ Net = [n \in Node |-> << >>]
    /\ SrvEnabled = [i \in Server |-> TRUE]
    /\ cliLeader = [c \in Client |-> Nil]
    /\ cliReq = [c \in Client |-> [type |-> PutT, key |-> CHOOSE k \in Key : TRUE, value |-> CHOOSE v \in Value : TRUE, idx |-> 0]]
    /\ cliReqIdx = [c \in Client |-> 0]
    /\ cliTimeout = [c \in Client |-> FALSE]

Tick(i) ==
    /\ i \in Server
    /\ SrvEnabled[i]
    /\ Timer' = [Timer EXCEPT ![i] = TRUE]
    /\ UNCHANGED << state, currentTerm, votedFor, leader, log, commitIndex, lastApplied,
                   nextIndex, matchIndex, votesResponded, votesGranted, sm, smDomain,
                   Net, SrvEnabled, cliLeader, cliReq, cliReqIdx, cliTimeout >>

StartElection(i) ==
    /\ i \in Server
    /\ SrvEnabled[i]
    /\ Timer[i]
    /\ state[i] \in {StateFollower, StateCandidate}
    /\ Len(Net[i]) = 0
    /\ LET newTerm == currentTerm[i] + 1 IN
       /\ state' = [state EXCEPT ![i] = StateCandidate]
       /\ currentTerm' = [currentTerm EXCEPT ![i] = newTerm]
       /\ votedFor' = [votedFor EXCEPT ![i] = i]
       /\ votesResponded' = [votesResponded EXCEPT ![i] = {i}]
       /\ votesGranted' = [votesGranted EXCEPT ![i] = {i}]
       /\ leader' = [leader EXCEPT ![i] = Nil]
       /\ Timer' = [Timer EXCEPT ![i] = FALSE]
       /\ Net' =
            [n \in Node |->
                IF n \in Server /\ n # i THEN
                    Append(Net[n],
                        [ mtype |-> RequestVoteRequestT,
                          mterm |-> newTerm,
                          msource |-> i,
                          mdest |-> n,
                          mlastLogIndex |-> Len(log[i]),
                          mlastLogTerm |-> LastTerm(log[i]),
                          mvoteGranted |-> FALSE,
                          mprevLogIndex |-> 0,
                          mprevLogTerm |-> 0,
                          mentries |-> << >>,
                          mcommitIndex |-> 0,
                          msuccess |-> FALSE,
                          mmatchIndex |-> 0,
                          mcmd |-> [type |-> PutT, key |-> CHOOSE k \in Key : TRUE, value |-> CHOOSE v \in Value : TRUE, idx |-> 0],
                          mleaderHint |-> Nil,
                          mresponse |-> [idx |-> 0, key |-> CHOOSE k \in Key : TRUE, value |-> Nil, ok |-> FALSE]
                        ])
                ELSE Net[n] ]
       /\ UNCHANGED << log, commitIndex, lastApplied, nextIndex, matchIndex, sm, smDomain, SrvEnabled, cliLeader, cliReq, cliReqIdx, cliTimeout >>

DeliverRVQ(i, pos) ==
    /\ i \in Server
    /\ SrvEnabled[i]
    /\ pos \in 1..Len(Net[i])
    /\ Net[i][pos].mtype = RequestVoteRequestT
    /\ LET m == Net[i][pos] IN
       LET termAfter == IF m.mterm > currentTerm[i] THEN m.mterm ELSE currentTerm[i] IN
       LET stateAfter == IF m.mterm > currentTerm[i] THEN StateFollower ELSE state[i] IN
       LET votedAfter == IF m.mterm > currentTerm[i] THEN Nil ELSE votedFor[i] IN
       LET leaderAfter == IF m.mterm > currentTerm[i] THEN Nil ELSE leader[i] IN
       LET grant == /\ m.mterm = termAfter
                    /\ stateAfter = StateFollower
                    /\ LogUpToDate(m.mlastLogTerm, m.mlastLogIndex, log[i])
                    /\ votedAfter \in {Nil, m.msource} IN
       /\ currentTerm' = [currentTerm EXCEPT ![i] = termAfter]
       /\ state' = [state EXCEPT ![i] = stateAfter]
       /\ votedFor' = [votedFor EXCEPT ![i] = IF grant THEN m.msource ELSE votedAfter]
       /\ leader' = [leader EXCEPT ![i] = leaderAfter]
       /\ Net' = [n \in Node |->
                    IF n = i THEN RemoveAt1(Net[i], pos)
                    ELSE IF n = m.msource THEN
                        Append(Net[n],
                          [ mtype |-> RequestVoteResponseT,
                            mterm |-> termAfter,
                            msource |-> i,
                            mdest |-> m.msource,
                            mlastLogIndex |-> 0,
                            mlastLogTerm |-> 0,
                            mvoteGranted |-> grant,
                            mprevLogIndex |-> 0,
                            mprevLogTerm |-> 0,
                            mentries |-> << >>,
                            mcommitIndex |-> 0,
                            msuccess |-> FALSE,
                            mmatchIndex |-> 0,
                            mcmd |-> [type |-> PutT, key |-> CHOOSE k \in Key : TRUE, value |-> CHOOSE v \in Value : TRUE, idx |-> 0],
                            mleaderHint |-> Nil,
                            mresponse |-> [idx |-> 0, key |-> CHOOSE k \in Key : TRUE, value |-> Nil, ok |-> FALSE]
                          ])
                    ELSE Net[n] ]
       /\ UNCHANGED << votesResponded, votesGranted, log, commitIndex, lastApplied, nextIndex, matchIndex, Timer, sm, smDomain, SrvEnabled, cliLeader, cliReq, cliReqIdx, cliTimeout >>

DeliverRVP(i, pos) ==
    /\ i \in Server
    /\ SrvEnabled[i]
    /\ pos \in 1..Len(Net[i])
    /\ Net[i][pos].mtype = RequestVoteResponseT
    /\ LET m == Net[i][pos] IN
       LET termAfter == IF m.mterm > currentTerm[i] THEN m.mterm ELSE currentTerm[i] IN
       LET stepDown == m.mterm > currentTerm[i] IN
       /\ currentTerm' = [currentTerm EXCEPT ![i] = termAfter]
       /\ state' = [state EXCEPT ![i] = IF stepDown THEN StateFollower ELSE state[i]]
       /\ votedFor' = [votedFor EXCEPT ![i] = IF stepDown THEN Nil ELSE votedFor[i]]
       /\ leader' = [leader EXCEPT ![i] = IF stepDown THEN Nil ELSE leader[i]]
       /\ votesResponded' = [votesResponded EXCEPT ![i] = IF m.mterm = termAfter THEN votesResponded[i] \cup {m.msource} ELSE votesResponded[i]]
       /\ votesGranted' = [votesGranted EXCEPT ![i] =
            IF /\ m.mterm = termAfter /\ m.mvoteGranted
               THEN votesGranted[i] \cup {m.msource}
               ELSE votesGranted[i] ]
       /\ Timer' = [Timer EXCEPT ![i] = IF /\ m.mterm = termAfter /\ m.mvoteGranted THEN FALSE ELSE Timer[i]]
       /\ Net' = [n \in Node |->
                    IF n = i THEN RemoveAt1(Net[i], pos) ELSE Net[n] ]
       /\ UNCHANGED << log, commitIndex, lastApplied, nextIndex, matchIndex, sm, smDomain, SrvEnabled, cliLeader, cliReq, cliReqIdx, cliTimeout >>

BecomeLeader(i) ==
    /\ i \in Server
    /\ SrvEnabled[i]
    /\ state[i] = StateCandidate
    /\ IsQuorum(votesGranted[i])
    /\ state' = [state EXCEPT ![i] = StateLeader]
    /\ leader' = [leader EXCEPT ![i] = i]
    /\ nextIndex' = [nextIndex EXCEPT ![i] = [j \in Server |-> Len(log[i]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![i] = [j \in Server |-> 0]]
    /\ UNCHANGED << currentTerm, votedFor, votesResponded, votesGranted, log, commitIndex, lastApplied, Timer, sm, smDomain, Net, SrvEnabled, cliLeader, cliReq, cliReqIdx, cliTimeout >>

AppendEntriesSend(i, j) ==
    /\ i \in Server /\ j \in Server /\ i # j
    /\ SrvEnabled[i]
    /\ state[i] = StateLeader
    /\ LET prevIdx == nextIndex[i][j] - 1 IN
       LET prevTerm == IF prevIdx > 0 THEN log[i][prevIdx].term ELSE 0 IN
       LET entries == EntriesFrom(log[i], nextIndex[i][j]) IN
       /\ Net' = [n \in Node |->
                    IF n = j THEN
                      Append(Net[n],
                        [ mtype |-> AppendEntriesRequestT,
                          mterm |-> currentTerm[i],
                          msource |-> i,
                          mdest |-> j,
                          mlastLogIndex |-> 0,
                          mlastLogTerm |-> 0,
                          mvoteGranted |-> FALSE,
                          mprevLogIndex |-> prevIdx,
                          mprevLogTerm |-> prevTerm,
                          mentries |-> entries,
                          mcommitIndex |-> commitIndex[i],
                          msuccess |-> FALSE,
                          mmatchIndex |-> 0,
                          mcmd |-> [type |-> PutT, key |-> CHOOSE k \in Key : TRUE, value |-> CHOOSE v \in Value : TRUE, idx |-> 0],
                          mleaderHint |-> Nil,
                          mresponse |-> [idx |-> 0, key |-> CHOOSE k \in Key : TRUE, value |-> Nil, ok |-> FALSE]
                        ])
                    ELSE Net[n] ]
       /\ UNCHANGED << state, currentTerm, votedFor, leader, log, commitIndex, lastApplied, nextIndex, matchIndex, votesResponded, votesGranted, Timer, sm, smDomain, SrvEnabled, cliLeader, cliReq, cliReqIdx, cliTimeout >>

DeliverAPQ(i, pos) ==
    /\ i \in Server
    /\ SrvEnabled[i]
    /\ pos \in 1..Len(Net[i])
    /\ Net[i][pos].mtype = AppendEntriesRequestT
    /\ LET m == Net[i][pos] IN
       LET termAfter == IF m.mterm > currentTerm[i] THEN m.mterm ELSE currentTerm[i] IN
       LET stAfter == IF m.mterm > currentTerm[i] THEN StateFollower ELSE state[i] IN
       LET votedAfter == IF m.mterm > currentTerm[i] THEN Nil ELSE votedFor[i] IN
       LET leadAfter == IF m.mterm > currentTerm[i] THEN Nil ELSE leader[i] IN
       LET equalTerm == m.mterm = termAfter IN
       LET stAfter2 == IF /\ equalTerm /\ stAfter = StateCandidate THEN StateFollower ELSE stAfter IN
       LET leaderAfter2 == IF equalTerm THEN m.msource ELSE leadAfter IN
       LET timerAfter == IF equalTerm THEN FALSE ELSE Timer[i] IN
       LET okPrev == FollowerLogOK(m.mprevLogIndex, m.mprevLogTerm, log[i]) IN
       LET newLog == IF /\ equalTerm /\ stAfter2 = StateFollower /\ okPrev
                     THEN SubSeq(log[i], 1, m.mprevLogIndex) \o m.mentries
                     ELSE log[i] IN
       LET newCommitRaw == IF /\ equalTerm /\ stAfter2 = StateFollower /\ okPrev
                           THEN m.mcommitIndex
                           ELSE commitIndex[i] IN
       LET newCommit == IF newCommitRaw <= Len(newLog)
                        THEN MaxNat({newCommitRaw, commitIndex[i]})
                        ELSE commitIndex[i] IN
       LET applyFrom == lastApplied[i] + 1 IN
       LET applyTo == newCommit IN
       LET applyEntries ==
            IF /\ equalTerm /\ stAfter2 = StateFollower /\ okPrev
               THEN TRUE ELSE FALSE IN
       /\ currentTerm' = [currentTerm EXCEPT ![i] = termAfter]
       /\ state' = [state EXCEPT ![i] = stAfter2]
       /\ votedFor' = [votedFor EXCEPT ![i] = votedAfter]
       /\ leader' = [leader EXCEPT ![i] = leaderAfter2]
       /\ Timer' = [Timer EXCEPT ![i] = timerAfter]
       /\ log' = [log EXCEPT ![i] = newLog]
       /\ commitIndex' = [commitIndex EXCEPT ![i] = newCommit]
       /\ sm' =
            IF /\ applyEntries /\ applyFrom <= applyTo
            THEN
                LET res == ApplyEntry(newLog[applyFrom], sm[i], smDomain[i]) IN
                [sm EXCEPT ![i] = res[1]]
            ELSE sm
       /\ smDomain' =
            IF /\ applyEntries /\ applyFrom <= applyTo
            THEN
                LET res == ApplyEntry(newLog[applyFrom], sm[i], smDomain[i]) IN
                [smDomain EXCEPT ![i] = res[2]]
            ELSE smDomain
       /\ lastApplied' =
            IF /\ applyEntries /\ applyFrom <= applyTo
            THEN [lastApplied EXCEPT ![i] = applyFrom]
            ELSE lastApplied
       /\ Net' = [n \in Node |->
                    IF n = i THEN RemoveAt1(Net[i], pos)
                    ELSE IF n = m.msource THEN
                        Append(Net[n],
                          [ mtype |-> AppendEntriesResponseT,
                            mterm |-> termAfter,
                            msource |-> i,
                            mdest |-> m.msource,
                            mlastLogIndex |-> 0,
                            mlastLogTerm |-> 0,
                            mvoteGranted |-> FALSE,
                            mprevLogIndex |-> 0,
                            mprevLogTerm |-> 0,
                            mentries |-> << >>,
                            mcommitIndex |-> 0,
                            msuccess |-> /\ equalTerm /\ stAfter2 = StateFollower /\ okPrev,
                            mmatchIndex |-> IF /\ equalTerm /\ stAfter2 = StateFollower /\ okPrev
                                             THEN m.mprevLogIndex + Len(m.mentries)
                                             ELSE 0,
                            mcmd |-> [type |-> PutT, key |-> CHOOSE k \in Key : TRUE, value |-> CHOOSE v \in Value : TRUE, idx |-> 0],
                            mleaderHint |-> Nil,
                            mresponse |-> [idx |-> 0, key |-> CHOOSE k \in Key : TRUE, value |-> Nil, ok |-> FALSE]
                          ])
                    ELSE Net[n] ]
       /\ UNCHANGED << votesResponded, votesGranted, nextIndex, matchIndex, SrvEnabled, cliLeader, cliReq, cliReqIdx, cliTimeout >>

DeliverAPP(i, pos) ==
    /\ i \in Server
    /\ SrvEnabled[i]
    /\ pos \in 1..Len(Net[i])
    /\ Net[i][pos].mtype = AppendEntriesResponseT
    /\ LET m == Net[i][pos] IN
       LET termAfter == IF m.mterm > currentTerm[i] THEN m.mterm ELSE currentTerm[i] IN
       LET stepDown == m.mterm > currentTerm[i] IN
       /\ currentTerm' = [currentTerm EXCEPT ![i] = termAfter]
       /\ state' = [state EXCEPT ![i] = IF stepDown THEN StateFollower ELSE state[i]]
       /\ votedFor' = [votedFor EXCEPT ![i] = IF stepDown THEN Nil ELSE votedFor[i]]
       /\ leader' = [leader EXCEPT ![i] = IF stepDown THEN Nil ELSE leader[i]]
       /\ Timer' = [Timer EXCEPT ![i] = IF m.mterm = termAfter THEN FALSE ELSE Timer[i]]
       /\ nextIndex' =
            IF /\ m.mterm = termAfter /\ state[i] = StateLeader
            THEN
                IF m.msuccess
                THEN [nextIndex EXCEPT ![i] = [nextIndex[i] EXCEPT ![m.msource] = m.mmatchIndex + 1]]
                ELSE [nextIndex EXCEPT ![i] = [nextIndex[i] EXCEPT ![m.msource] = MaxNat({nextIndex[i][m.msource] - 1, 1})]]
            ELSE nextIndex
       /\ matchIndex' =
            IF /\ m.mterm = termAfter /\ state[i] = StateLeader /\ m.msuccess
            THEN [matchIndex EXCEPT ![i] = [matchIndex[i] EXCEPT ![m.msource] = m.mmatchIndex]]
            ELSE matchIndex
       /\ Net' = [n \in Node |->
                    IF n = i THEN RemoveAt1(Net[i], pos) ELSE Net[n] ]
       /\ UNCHANGED << votesResponded, votesGranted, log, commitIndex, lastApplied, sm, smDomain, SrvEnabled, cliLeader, cliReq, cliReqIdx, cliTimeout >>

AdvanceCommit(i) ==
    /\ i \in Server
    /\ SrvEnabled[i]
    /\ state[i] = StateLeader
    /\ LET N == FindMaxAgreeIndex(i) IN
       /\ commitIndex' = [commitIndex EXCEPT ![i] =
            IF /\ N > commitIndex[i]
               /\ N <= Len(log[i])
               /\ log[i][N].term = currentTerm[i]
            THEN N ELSE commitIndex[i] ]
       /\ UNCHANGED << state, currentTerm, votedFor, leader, log, lastApplied,
                      nextIndex, matchIndex, votesResponded, votesGranted, Timer,
                      sm, smDomain, Net, SrvEnabled, cliLeader, cliReq, cliReqIdx, cliTimeout >>

ApplyCommitted(i) ==
    /\ i \in Server
    /\ SrvEnabled[i]
    /\ lastApplied[i] < commitIndex[i]
    /\ LET k == lastApplied[i] + 1 IN
       LET e == log[i][k] IN
       LET res == ApplyEntry(e, sm[i], smDomain[i]) IN
       /\ sm' = [sm EXCEPT ![i] = res[1]]
       /\ smDomain' = [smDomain EXCEPT ![i] = res[2]]
       /\ lastApplied' = [lastApplied EXCEPT ![i] = k]
       /\ Net' =
            IF state[i] = StateLeader
            THEN
                LET ok == IF e.cmd.type = GetT THEN e.cmd.key \in smDomain'[i] ELSE TRUE IN
                LET val == IF /\ e.cmd.type = GetT /\ ok THEN sm'[i][e.cmd.key] ELSE Nil IN
                LET rtype == IF e.cmd.type = PutT THEN ClientPutResponseT ELSE ClientGetResponseT IN
                [n \in Node |->
                    IF n = e.client THEN
                        Append(Net[n],
                          [ mtype |-> rtype,
                            mterm |-> currentTerm[i],
                            msource |-> i,
                            mdest |-> e.client,
                            mlastLogIndex |-> 0,
                            mlastLogTerm |-> 0,
                            mvoteGranted |-> FALSE,
                            mprevLogIndex |-> 0,
                            mprevLogTerm |-> 0,
                            mentries |-> << >>,
                            mcommitIndex |-> 0,
                            msuccess |-> TRUE,
                            mmatchIndex |-> 0,
                            mcmd |-> [type |-> e.cmd.type, key |-> e.cmd.key, value |-> e.cmd.value, idx |-> e.cmd.idx],
                            mleaderHint |-> i,
                            mresponse |-> [idx |-> e.cmd.idx, key |-> e.cmd.key, value |-> val, ok |-> ok]
                          ])
                    ELSE Net[n] ]
            ELSE Net
       /\ UNCHANGED << state, currentTerm, votedFor, leader, log, commitIndex,
                      nextIndex, matchIndex, votesResponded, votesGranted, Timer, SrvEnabled,
                      cliLeader, cliReq, cliReqIdx, cliTimeout >>

DeliverClientReq(i, pos) ==
    /\ i \in Server
    /\ SrvEnabled[i]
    /\ pos \in 1..Len(Net[i])
    /\ Net[i][pos].mtype \in {ClientPutRequestT, ClientGetRequestT}
    /\ LET m == Net[i][pos] IN
       IF state[i] = StateLeader THEN
         /\ log' = [log EXCEPT ![i] = Append(log[i],
                    [ term |-> currentTerm[i],
                      cmd |-> m.mcmd,
                      client |-> m.msource ])]
         /\ Net' = [n \in Node |->
                      IF n = i THEN RemoveAt1(Net[i], pos) ELSE Net[n] ]
         /\ UNCHANGED << state, currentTerm, votedFor, leader, commitIndex, lastApplied,
                        nextIndex, matchIndex, votesResponded, votesGranted, Timer, sm, smDomain,
                        SrvEnabled, cliLeader, cliReq, cliReqIdx, cliTimeout >>
       ELSE
         /\ Net' = [n \in Node |->
                      IF n = i THEN RemoveAt1(Net[i], pos)
                      ELSE IF n = m.msource THEN
                        Append(Net[n],
                          [ mtype |-> IF m.mtype = ClientPutRequestT THEN ClientPutResponseT ELSE ClientGetResponseT,
                            mterm |-> currentTerm[i],
                            msource |-> i,
                            mdest |-> m.msource,
                            mlastLogIndex |-> 0,
                            mlastLogTerm |-> 0,
                            mvoteGranted |-> FALSE,
                            mprevLogIndex |-> 0,
                            mprevLogTerm |-> 0,
                            mentries |-> << >>,
                            mcommitIndex |-> 0,
                            msuccess |-> FALSE,
                            mmatchIndex |-> 0,
                            mcmd |-> m.mcmd,
                            mleaderHint |-> leader[i],
                            mresponse |-> [idx |-> m.mcmd.idx, key |-> m.mcmd.key, value |-> Nil, ok |-> FALSE]
                          ])
                      ELSE Net[n] ]
         /\ UNCHANGED << state, currentTerm, votedFor, leader, log, commitIndex, lastApplied,
                        nextIndex, matchIndex, votesResponded, votesGranted, Timer, sm, smDomain,
                        SrvEnabled, cliLeader, cliReq, cliReqIdx, cliTimeout >>

DeliverClientResp(c, pos) ==
    /\ c \in Client
    /\ pos \in 1..Len(Net[c])
    /\ Net[c][pos].mtype \in {ClientPutResponseT, ClientGetResponseT}
    /\ LET m == Net[c][pos] IN
       /\ cliLeader' = [cliLeader EXCEPT ![c] = m.mleaderHint]
       /\ IF m.msuccess THEN
            /\ cliReq' = [cliReq EXCEPT ![c] = cliReq[c]]
            /\ cliReqIdx' = cliReqIdx
          ELSE
            /\ cliReq' = [cliReq EXCEPT ![c] = cliReq[c]]
            /\ cliReqIdx' = cliReqIdx
       /\ Net' = [n \in Node |->
                    IF n = c THEN RemoveAt1(Net[c], pos) ELSE Net[n] ]
       /\ UNCHANGED << state, currentTerm, votedFor, leader, log, commitIndex, lastApplied,
                      nextIndex, matchIndex, votesResponded, votesGranted, Timer, sm, smDomain, SrvEnabled, cliTimeout >>

ClientSend(c) ==
    /\ c \in Client
    /\ LET dest == IF cliLeader[c] = Nil THEN CHOOSE s \in Server : TRUE ELSE cliLeader[c] IN
       LET newIdx == cliReqIdx[c] + 1 IN
       LET pickKey == CHOOSE k \in Key : TRUE IN
       LET pickVal == CHOOSE v \in Value : TRUE IN
       LET isPut == CHOOSE b \in {TRUE, FALSE} : TRUE IN
       LET cmd == [ type |-> IF isPut THEN PutT ELSE GetT,
                    key |-> pickKey,
                    value |-> IF isPut THEN pickVal ELSE Nil,
                    idx |-> newIdx ] IN
       /\ cliReqIdx' = [cliReqIdx EXCEPT ![c] = newIdx]
       /\ cliLeader' = [cliLeader EXCEPT ![c] = dest]
       /\ Net' = [n \in Node |->
                    IF n = dest THEN
                      Append(Net[n],
                        [ mtype |-> IF isPut THEN ClientPutRequestT ELSE ClientGetRequestT,
                          mterm |-> 0,
                          msource |-> c,
                          mdest |-> dest,
                          mlastLogIndex |-> 0,
                          mlastLogTerm |-> 0,
                          mvoteGranted |-> FALSE,
                          mprevLogIndex |-> 0,
                          mprevLogTerm |-> 0,
                          mentries |-> << >>,
                          mcommitIndex |-> 0,
                          msuccess |-> FALSE,
                          mmatchIndex |-> 0,
                          mcmd |-> cmd,
                          mleaderHint |-> Nil,
                          mresponse |-> [idx |-> 0, key |-> pickKey, value |-> Nil, ok |-> FALSE]
                        ])
                    ELSE Net[n] ]
       /\ UNCHANGED << state, currentTerm, votedFor, leader, log, commitIndex, lastApplied,
                      nextIndex, matchIndex, votesResponded, votesGranted, Timer, sm, smDomain, SrvEnabled, cliReq, cliTimeout >>

Drop(n, pos) ==
    /\ n \in Node
    /\ pos \in 1..Len(Net[n])
    /\ Net' = [x \in Node |->
                 IF x = n THEN RemoveAt1(Net[n], pos) ELSE Net[x] ]
    /\ UNCHANGED << state, currentTerm, votedFor, leader, log, commitIndex, lastApplied,
                   nextIndex, matchIndex, votesResponded, votesGranted, Timer, sm, smDomain,
                   SrvEnabled, cliLeader, cliReq, cliReqIdx, cliTimeout >>

Crash(i) ==
    /\ i \in Server
    /\ SrvEnabled[i]
    /\ SrvEnabled' = [SrvEnabled EXCEPT ![i] = FALSE]
    /\ UNCHANGED << state, currentTerm, votedFor, leader, log, commitIndex, lastApplied,
                   nextIndex, matchIndex, votesResponded, votesGranted, Timer, sm, smDomain,
                   Net, cliLeader, cliReq, cliReqIdx, cliTimeout >>

Next ==
    \/
      \E i \in Server : Tick(i)
    \/
      \E i \in Server : StartElection(i)
    \/
      \E i,j \in Server : AppendEntriesSend(i, j)
    \/
      \E i \in Server, pos \in 1..Len(Net[i]) : DeliverRVQ(i, pos)
    \/
      \E i \in Server, pos \in 1..Len(Net[i]) : DeliverRVP(i, pos)
    \/
      \E i \in Server, pos \in 1..Len(Net[i]) : DeliverAPQ(i, pos)
    \/
      \E i \in Server, pos \in 1..Len(Net[i]) : DeliverAPP(i, pos)
    \/
      \E i \in Server, pos \in 1..Len(Net[i]) : DeliverClientReq(i, pos)
    \/
      \E c \in Client, pos \in 1..Len(Net[c]) : DeliverClientResp(c, pos)
    \/
      \E c \in Client : ClientSend(c)
    \/
      \E i \in Server : BecomeLeader(i)
    \/
      \E i \in Server : AdvanceCommit(i)
    \/
      \E i \in Server : ApplyCommitted(i)
    \/
      \E n \in Node, pos \in 1..Len(Net[n]) : Drop(n, pos)
    \/
      \E i \in Server : Crash(i)

Spec ==
    Init /\ [][Next]_vars
    /\ WF_vars(\E i \in Server : StartElection(i))
    /\ WF_vars(\E i \in Server, pos \in 1..Len(Net[i]) : DeliverAPQ(i, pos) \/ DeliverAPP(i, pos) \/ DeliverRVQ(i, pos) \/ DeliverRVP(i, pos) \/ DeliverClientReq(i, pos))
    /\ WF_vars(\E i,j \in Server : AppendEntriesSend(i, j))
    /\ WF_vars(\E i \in Server : AdvanceCommit(i))
    /\ WF_vars(\E i \in Server : ApplyCommitted(i))
    /\ WF_vars(\E c \in Client : ClientSend(c))

====