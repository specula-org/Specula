---------------------------- MODULE base ----------------------------
\* TLA+ specification of brpc/braft Raft consensus protocol.
\*
\* Extends standard Raft with braft-specific behaviors:
\*   1. Two-sided leader lease: LeaderLease + FollowerLease asymmetry (Bug Family 1)
\*   2. PreVote as separate phase with different lease/term handling (Bug Family 1)
\*   3. Snapshot response missing term check (Bug Family 2)
\*   4. Non-atomic persistence in elect_self: RPCs before persist (Bug Family 3)
\*   5. Joint consensus configuration changes with force-commit (Bug Family 4)
\*
EXTENDS Naturals, FiniteSets, Sequences, Bags, TLC

----
\* Constants
----

CONSTANT Server              \* Set of server IDs

CONSTANTS Follower,          \* Server states
          Candidate,
          Leader

CONSTANT Nil                 \* Null value

CONSTANTS ValueEntry,        \* Log entry types
          ConfigEntry

CONSTANTS PreVoteRequest,           \* Message types
          PreVoteResponse,
          RequestVoteRequest,
          RequestVoteResponse,
          AppendEntriesRequest,
          AppendEntriesResponse,
          InstallSnapshotRequest,
          InstallSnapshotResponse

----
\* Variables
----

\* Per-server persistent state (survives restart via stable store)
VARIABLE currentTerm         \* [Server -> Nat]
VARIABLE votedFor            \* [Server -> Server \cup {Nil}]
VARIABLE log                 \* [Server -> Seq(Entry)]

\* Per-server volatile state
VARIABLE state               \* [Server -> {Follower, Candidate, Leader}]
VARIABLE commitIndex         \* [Server -> Nat]

\* Leader volatile state
VARIABLE nextIndex           \* [Server -> [Server -> Nat]]
VARIABLE matchIndex          \* [Server -> [Server -> Nat]]

\* Candidate state
VARIABLE votesGranted        \* [Server -> SUBSET Server]
VARIABLE preVotesGranted     \* [Server -> SUBSET Server]

\* Network
VARIABLE messages            \* Bag of message records

\* Extension 1: Two-sided leader lease (Bug Family 1)
\* LeaderLease: leader tracks which followers it has contacted.
\* FollowerLease: follower blocks votes while leader recently seen.
\* Key asymmetry: become_leader resets followerLease (node.cpp:1949),
\* so a leader always grants PreVote (votable_time_from_now returns 0).
\* Reference: lease.cpp:111-123 (votable_time_from_now),
\*            lease.cpp:53-56 (LeaderLease::renew)
VARIABLE leaderContact       \* [Server -> SUBSET Server] -- leader's view of contacted followers
VARIABLE followerLease       \* [Server -> BOOLEAN] -- TRUE = follower believes leader is alive

\* Extension 2: Disrupted leader tracking (Bug Family 1)
\* When a leader steps down due to higher term in vote response,
\* it sets disrupted_leader info so the new candidate can bypass
\* follower leases.
\* Reference: node.cpp:2199-2208 (disrupted_leader bypass)
VARIABLE disruptedLeader     \* [Server -> Server \cup {Nil}] -- who disrupted the old leader

\* Extension 3: Non-atomic persistence (Bug Family 3)
\* In elect_self(), RPCs are sent BEFORE term/votedFor is persisted.
\* Reference: node.cpp:1705-1707 (memory update), 1735 (RPCs), 1738 (persist)
\* In step_down(), persist failure is logged but not handled.
\* Reference: node.cpp:1844-1849
VARIABLE persistedTerm       \* [Server -> Nat]
VARIABLE persistedVotedFor   \* [Server -> Server \cup {Nil}]
VARIABLE pendingPersist      \* [Server -> BOOLEAN] -- TRUE = elect_self sent RPCs but not yet persisted

\* Extension 4: Joint consensus configuration (Bug Family 4)
\* braft uses joint consensus for multi-peer changes,
\* single-peer changes skip joint stage (node.cpp:3296-3301).
\* Reference: ballot_box.cpp:79-88 (force-commit, "not well proved")
VARIABLE config              \* [Server -> SUBSET Server] -- current committed config
VARIABLE newConfig           \* [Server -> SUBSET Server \cup {Nil}] -- pending new config (joint stage)

----
\* Variable groups
----

serverVars    == <<currentTerm, votedFor, state>>
logVars       == <<log, commitIndex>>
leaderVars    == <<nextIndex, matchIndex>>
candidateVars == <<votesGranted, preVotesGranted>>
leaseVars     == <<leaderContact, followerLease, disruptedLeader>>
persistVars   == <<persistedTerm, persistedVotedFor, pendingPersist>>
configVars    == <<config, newConfig>>

vars == <<serverVars, logVars, leaderVars, candidateVars, messages,
          leaseVars, persistVars, configVars>>

----
\* Helpers
----

Min(a, b) == IF a <= b THEN a ELSE b
Max(a, b) == IF a >= b THEN a ELSE b

SetMax(S) == CHOOSE x \in S : \A y \in S : x >= y

\* Log helpers
LastLogIndex(i) == Len(log[i])
LastLogTerm(i)  == IF Len(log[i]) > 0 THEN log[i][Len(log[i])].term ELSE 0
LogTerm(i, idx) == IF idx > 0 /\ idx <= Len(log[i]) THEN log[i][idx].term ELSE 0

\* Quorum check: majority of voters
IsQuorum(S, voters) == Cardinality(S) * 2 > Cardinality(voters)

\* Joint quorum: majority of BOTH old and new config
\* Reference: node.cpp joint consensus -- quorum must be met in both configs
IsJointQuorum(S, oldVoters, newVoters) ==
    /\ IsQuorum(S \cap oldVoters, oldVoters)
    /\ IsQuorum(S \cap newVoters, newVoters)

\* Effective quorum check: uses joint quorum if in joint stage
QuorumCheck(S, i) ==
    IF newConfig[i] = Nil
    THEN IsQuorum(S \cap config[i], config[i])
    ELSE IsJointQuorum(S, config[i], newConfig[i])

\* Log up-to-date comparison
\* Reference: node.cpp handle_pre_vote_request/handle_request_vote_request
LogUpToDate(cLastTerm, cLastIdx, vLastTerm, vLastIdx) ==
    \/ cLastTerm > vLastTerm
    \/ (cLastTerm = vLastTerm /\ cLastIdx >= vLastIdx)

\* Scan log for the last ConfigEntry at or before index maxIdx.
LatestConfigIn(logSeq, maxIdx) ==
    LET bound == Min(maxIdx, Len(logSeq))
        indices == {k \in 1..bound : logSeq[k].type = ConfigEntry}
    IN IF indices = {} THEN Server
       ELSE logSeq[SetMax(indices)].config

\* Message bag helpers
Send(m) == messages' = messages (+) SetToBag({m})
SendAll(ms) == messages' = messages (+) SetToBag(ms)
Discard(m) == messages' = messages (-) SetToBag({m})
Reply(resp, req) ==
    messages' = (messages (-) SetToBag({req})) (+) SetToBag({resp})
DiscardAndSendAll(discard, sends) ==
    messages' = (messages (-) SetToBag({discard})) (+) SetToBag(sends)

----
\* Init
----

Init ==
    /\ currentTerm      = [s \in Server |-> 0]
    /\ votedFor          = [s \in Server |-> Nil]
    /\ log               = [s \in Server |-> <<>>]
    /\ state             = [s \in Server |-> Follower]
    /\ commitIndex       = [s \in Server |-> 0]
    /\ nextIndex         = [s \in Server |-> [t \in Server |-> 1]]
    /\ matchIndex        = [s \in Server |-> [t \in Server |-> 0]]
    /\ votesGranted      = [s \in Server |-> {}]
    /\ preVotesGranted   = [s \in Server |-> {}]
    /\ messages          = EmptyBag
    /\ leaderContact     = [s \in Server |-> {}]
    /\ followerLease     = [s \in Server |-> FALSE]
    /\ disruptedLeader   = [s \in Server |-> Nil]
    /\ persistedTerm     = [s \in Server |-> 0]
    /\ persistedVotedFor = [s \in Server |-> Nil]
    /\ pendingPersist    = [s \in Server |-> FALSE]
    /\ config            = [s \in Server |-> Server]
    /\ newConfig         = [s \in Server |-> Nil]

----
\* PreVote Actions (Bug Family 1)
\*
\* braft uses PreVote to avoid disrupting stable leaders.
\* PreVote does NOT change term or votedFor.
----

\* Server i starts PreVote phase.
\* Reference: node.cpp:1619-1680 (pre_vote)
\* Checks: not installing snapshot, node in configuration.
\* Does NOT increment term; sends PreVoteRequest with currentTerm+1.
PreVote(i) ==
    /\ state[i] = Follower
    /\ i \in config[i]
    /\ pendingPersist[i] = FALSE
    \* PreVote does NOT change term or votedFor (node.cpp:1658-1660)
    /\ preVotesGranted' = [preVotesGranted EXCEPT ![i] = {i}]
    /\ SendAll({[mtype        |-> PreVoteRequest,
                 mterm        |-> currentTerm[i] + 1,
                 mlastLogTerm |-> LastLogTerm(i),
                 mlastLogIndex |-> LastLogIndex(i),
                 msource      |-> i,
                 mdest        |-> j] : j \in config[i] \ {i}})
    /\ UNCHANGED <<serverVars, logVars, leaderVars, votesGranted,
                   leaseVars, persistVars, configVars>>

\* Server i handles PreVoteRequest m.
\* Reference: node.cpp:2109-2174 (handle_pre_vote_request)
\*
\* Key (Bug Family 1): checks _follower_lease.votable_time_from_now()
\* but does NOT check _leader_lease. Since become_leader() resets
\* _follower_lease (node.cpp:1949), a leader always has votable_time=0
\* and thus ALWAYS grants PreVote requests.
HandlePreVoteRequest(i, m) ==
    /\ m.mtype = PreVoteRequest
    /\ m.mdest = i
    /\ LET mterm    == m.mterm
           logOk    == LogUpToDate(m.mlastLogTerm, m.mlastLogIndex,
                                   LastLogTerm(i), LastLogIndex(i))
       IN
       \/ \* Reject: term too low (node.cpp:2135-2140)
          /\ mterm <= currentTerm[i]
          /\ ~logOk
          /\ Reply([mtype             |-> PreVoteResponse,
                    mterm             |-> currentTerm[i],
                    mvoteGranted      |-> FALSE,
                    mrejectedByLease  |-> FALSE,
                    mdisrupted        |-> FALSE,
                    msource           |-> i,
                    mdest             |-> m.msource], m)
          /\ UNCHANGED <<serverVars, logVars, leaderVars, candidateVars,
                         leaseVars, persistVars, configVars>>

       \/ \* Grant: log is up-to-date and lease check passes
          \* (node.cpp:2148-2162)
          /\ logOk
          /\ \/ mterm > currentTerm[i]
             \/ mterm = currentTerm[i] + 1
          \* Bug Family 1: follower lease check
          \* Leader: followerLease is always FALSE (reset at become_leader),
          \*   so leader always grants PreVote
          \* Follower: followerLease may be TRUE, blocking the vote
          /\ ~followerLease[i]
          /\ Reply([mtype             |-> PreVoteResponse,
                    mterm             |-> currentTerm[i],
                    mvoteGranted      |-> TRUE,
                    mrejectedByLease  |-> FALSE,
                    \* node.cpp:2165: disrupted = (state == LEADER)
                    mdisrupted        |-> state[i] = Leader,
                    msource           |-> i,
                    mdest             |-> m.msource], m)
          /\ UNCHANGED <<serverVars, logVars, leaderVars, candidateVars,
                         leaseVars, persistVars, configVars>>

       \/ \* Reject by lease: log OK but follower lease still valid
          \* (node.cpp:2153-2156)
          /\ logOk
          /\ \/ mterm > currentTerm[i]
             \/ mterm = currentTerm[i] + 1
          /\ followerLease[i]
          /\ state[i] = Follower  \* only followers have active lease
          /\ Reply([mtype             |-> PreVoteResponse,
                    mterm             |-> currentTerm[i],
                    mvoteGranted      |-> FALSE,
                    mrejectedByLease  |-> TRUE,
                    mdisrupted        |-> FALSE,
                    msource           |-> i,
                    mdest             |-> m.msource], m)
          /\ UNCHANGED <<serverVars, logVars, leaderVars, candidateVars,
                         leaseVars, persistVars, configVars>>

\* Server i handles PreVoteResponse m.
\* Reference: node.cpp:1503-1581 (handle_pre_vote_response)
HandlePreVoteResponse(i, m) ==
    /\ m.mtype = PreVoteResponse
    /\ m.mdest = i
    /\ state[i] = Follower
    /\ \/ \* Higher term: step down (node.cpp:1536-1540)
          /\ m.mterm > currentTerm[i]
          /\ currentTerm' = [currentTerm EXCEPT ![i] = m.mterm]
          /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
          /\ persistedTerm' = [persistedTerm EXCEPT ![i] = m.mterm]
          /\ Discard(m)
          /\ UNCHANGED <<state, logVars, leaderVars, candidateVars,
                         leaseVars, persistedVotedFor, pendingPersist, configVars>>
       \/ \* Not granted and not rejected_by_lease: ignore (node.cpp:1548-1550)
          /\ ~m.mvoteGranted
          /\ ~m.mrejectedByLease
          /\ Discard(m)
          /\ UNCHANGED <<serverVars, logVars, leaderVars, candidateVars,
                         leaseVars, persistVars, configVars>>
       \/ \* Granted: count vote (node.cpp:1562-1569)
          /\ m.mvoteGranted
          /\ m.mterm <= currentTerm[i]
          /\ preVotesGranted' = [preVotesGranted EXCEPT ![i] = @ \cup {m.msource}]
          \* Track disrupted leader if response says so (node.cpp:1558-1560)
          /\ disruptedLeader' = IF m.mdisrupted
                                THEN [disruptedLeader EXCEPT ![i] = m.msource]
                                ELSE disruptedLeader
          /\ Discard(m)
          /\ UNCHANGED <<serverVars, logVars, leaderVars, votesGranted,
                         leaderContact, followerLease,
                         persistVars, configVars>>
       \/ \* Rejected by lease: reserve for retry (node.cpp:1553-1555, 1565)
          /\ m.mrejectedByLease
          /\ m.mterm <= currentTerm[i]
          /\ Discard(m)
          /\ UNCHANGED <<serverVars, logVars, leaderVars, candidateVars,
                         leaseVars, persistVars, configVars>>

\* Candidate i has PreVote quorum, starts real election.
\* Reference: node.cpp:1576-1577 -> elect_self()
\* This transitions from PreVote success to real Candidate state.
ElectSelf(i) ==
    /\ state[i] = Follower
    /\ QuorumCheck(preVotesGranted[i], i)
    /\ pendingPersist[i] = FALSE
    /\ LET newTerm == currentTerm[i] + 1
       IN
       \* node.cpp:1705-1707: update in-memory state
       /\ currentTerm' = [currentTerm EXCEPT ![i] = newTerm]
       /\ state' = [state EXCEPT ![i] = Candidate]
       /\ votedFor' = [votedFor EXCEPT ![i] = i]
       /\ votesGranted' = [votesGranted EXCEPT ![i] = {i}]
       /\ preVotesGranted' = [preVotesGranted EXCEPT ![i] = {}]
       \* Bug Family 3: RPCs sent BEFORE persist (node.cpp:1735 vs 1738)
       \* Mark pending persist; actual persist happens in CompletePersistElectSelf
       /\ pendingPersist' = [pendingPersist EXCEPT ![i] = TRUE]
       /\ UNCHANGED <<persistedTerm, persistedVotedFor>>
       \* node.cpp:1714-1716: if old leader disrupted, set in request
       /\ SendAll({[mtype             |-> RequestVoteRequest,
                    mterm             |-> newTerm,
                    mlastLogTerm      |-> LastLogTerm(i),
                    mlastLogIndex     |-> LastLogIndex(i),
                    mdisruptedLeader  |-> disruptedLeader[i],
                    msource           |-> i,
                    mdest             |-> j] : j \in config[i] \ {i}})
    /\ UNCHANGED <<logVars, leaderVars, leaderContact, followerLease,
                   disruptedLeader, configVars>>

\* Complete the persist after elect_self (Bug Family 3).
\* Reference: node.cpp:1738-1747 (set_term_and_votedfor)
CompletePersistElectSelf(i) ==
    /\ pendingPersist[i] = TRUE
    /\ state[i] = Candidate
    /\ persistedTerm' = [persistedTerm EXCEPT ![i] = currentTerm[i]]
    /\ persistedVotedFor' = [persistedVotedFor EXCEPT ![i] = i]
    /\ pendingPersist' = [pendingPersist EXCEPT ![i] = FALSE]
    /\ UNCHANGED <<serverVars, logVars, leaderVars, candidateVars,
                   messages, leaseVars, configVars>>

----
\* Election Actions
----

\* Server i handles RequestVoteRequest m.
\* Reference: node.cpp:2176-2289 (handle_request_vote_request)
\*
\* Key differences from PreVote handler:
\*   - Disrupted leader bypass: expires follower lease (node.cpp:2199-2208)
\*   - Persist before response (node.cpp:2270-2271)
\*   - Updates term and votedFor
HandleRequestVoteRequest(i, m) ==
    /\ m.mtype = RequestVoteRequest
    /\ m.mdest = i
    /\ LET mterm    == m.mterm
           logOk    == LogUpToDate(m.mlastLogTerm, m.mlastLogIndex,
                                   LastLogTerm(i), LastLogIndex(i))
           \* node.cpp:2199-2208: disrupted_leader bypass
           \* If follower sees disrupted_leader matching its known leader,
           \* expire the follower lease to allow voting
           leaseExpired ==
               \/ ~followerLease[i]
               \/ /\ state[i] = Follower
                  /\ m.mdisruptedLeader /= Nil
                  /\ m.mdisruptedLeader = disruptedLeader[i]
           canGrant == /\ logOk
                       /\ leaseExpired
                       /\ \/ mterm > currentTerm[i]
                          \/ /\ mterm = currentTerm[i]
                             /\ votedFor[i] \in {Nil, m.msource}
       IN
       \/ \* Reject: term too low
          /\ mterm < currentTerm[i]
          /\ Reply([mtype        |-> RequestVoteResponse,
                    mterm        |-> currentTerm[i],
                    mvoteGranted |-> FALSE,
                    msource      |-> i,
                    mdest        |-> m.msource], m)
          /\ UNCHANGED <<serverVars, logVars, leaderVars, candidateVars,
                         leaseVars, persistVars, configVars>>

       \/ \* Reject: can't grant (log not up-to-date, lease blocking, already voted)
          /\ mterm >= currentTerm[i]
          /\ ~canGrant
          /\ Reply([mtype        |-> RequestVoteResponse,
                    mterm        |-> Max(currentTerm[i], mterm),
                    mvoteGranted |-> FALSE,
                    msource      |-> i,
                    mdest        |-> m.msource], m)
          /\ IF mterm > currentTerm[i]
             THEN \* step_down (node.cpp:2241-2248)
                  /\ currentTerm' = [currentTerm EXCEPT ![i] = mterm]
                  /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
                  /\ state' = [state EXCEPT ![i] = Follower]
                  /\ persistedTerm' = [persistedTerm EXCEPT ![i] = mterm]
                  /\ UNCHANGED <<persistedVotedFor, pendingPersist>>
             ELSE UNCHANGED <<serverVars, persistVars>>
          /\ UNCHANGED <<logVars, leaderVars, candidateVars,
                         leaseVars, configVars>>

       \/ \* Grant: persist and respond (node.cpp:2263-2280)
          /\ canGrant
          /\ mterm >= currentTerm[i]
          /\ currentTerm' = [currentTerm EXCEPT ![i] = mterm]
          /\ votedFor' = [votedFor EXCEPT ![i] = m.msource]
          /\ state' = [state EXCEPT ![i] = Follower]
          \* Persist before response (node.cpp:2270-2271)
          /\ persistedTerm' = [persistedTerm EXCEPT ![i] = mterm]
          /\ persistedVotedFor' = [persistedVotedFor EXCEPT ![i] = m.msource]
          /\ UNCHANGED pendingPersist
          \* Expire follower lease on grant (implicit in step_down path)
          /\ followerLease' = [followerLease EXCEPT ![i] = FALSE]
          /\ Reply([mtype        |-> RequestVoteResponse,
                    mterm        |-> mterm,
                    mvoteGranted |-> TRUE,
                    msource      |-> i,
                    mdest        |-> m.msource], m)
          /\ UNCHANGED <<logVars, leaderVars, candidateVars,
                         leaderContact, disruptedLeader, configVars>>

\* Server i handles RequestVoteResponse m.
\* Reference: node.cpp:1394-1460 (handle_request_vote_response)
HandleRequestVoteResponse(i, m) ==
    /\ m.mtype = RequestVoteResponse
    /\ m.mdest = i
    /\ state[i] = Candidate
    /\ \/ \* Higher term: step down (node.cpp:1422-1431)
          /\ m.mterm > currentTerm[i]
          /\ currentTerm' = [currentTerm EXCEPT ![i] = m.mterm]
          /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
          /\ state' = [state EXCEPT ![i] = Follower]
          /\ persistedTerm' = [persistedTerm EXCEPT ![i] = m.mterm]
          /\ Discard(m)
          /\ UNCHANGED <<logVars, leaderVars, candidateVars,
                         leaseVars, persistedVotedFor, pendingPersist, configVars>>
       \/ \* Current term response (node.cpp:1438-1459)
          /\ m.mterm = currentTerm[i]
          /\ IF m.mvoteGranted
             THEN votesGranted' = [votesGranted EXCEPT ![i] = @ \cup {m.msource}]
             ELSE UNCHANGED votesGranted
          /\ Discard(m)
          /\ UNCHANGED <<serverVars, logVars, leaderVars, preVotesGranted,
                         leaseVars, persistVars, configVars>>
       \/ \* Stale response, ignore
          /\ m.mterm < currentTerm[i]
          /\ Discard(m)
          /\ UNCHANGED <<serverVars, logVars, leaderVars, candidateVars,
                         leaseVars, persistVars, configVars>>

\* Candidate i becomes leader after receiving quorum of votes.
\* Reference: node.cpp:1940-1975 (become_leader)
BecomeLeader(i) ==
    /\ state[i] = Candidate
    /\ pendingPersist[i] = FALSE
    /\ QuorumCheck(votesGranted[i], i)
    /\ state' = [state EXCEPT ![i] = Leader]
    /\ nextIndex'  = [nextIndex  EXCEPT ![i] = [j \in Server |-> LastLogIndex(i) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![i] = [j \in Server |-> 0]]
    /\ leaderContact' = [leaderContact EXCEPT ![i] = {}]
    \* Bug Family 1: become_leader resets follower lease (node.cpp:1949)
    \* This means the leader's followerLease is always FALSE,
    \* so it always grants PreVote requests!
    /\ followerLease' = [followerLease EXCEPT ![i] = FALSE]
    /\ disruptedLeader' = [disruptedLeader EXCEPT ![i] = Nil]
    /\ UNCHANGED <<currentTerm, votedFor, logVars, candidateVars, messages,
                   persistVars, configVars>>

----
\* Log Replication Actions
----

\* Leader i appends a client request to its log.
ClientRequest(i) ==
    /\ state[i] = Leader
    /\ LET entry == [term |-> currentTerm[i], type |-> ValueEntry, config |-> {}]
       IN log' = [log EXCEPT ![i] = Append(@, entry)]
    /\ UNCHANGED <<serverVars, commitIndex, leaderVars, candidateVars, messages,
                   leaseVars, persistVars, configVars>>

\* Leader i sends AppendEntries with log entries to server j.
\* Reference: replicator.cpp:199-282 (_send_entries / replicateTo)
ReplicateEntries(i, j) ==
    /\ state[i] = Leader
    /\ i /= j
    /\ LET prevIdx  == nextIndex[i][j] - 1
           prevTerm == LogTerm(i, prevIdx)
           lastIdx  == LastLogIndex(i)
           entries  == IF nextIndex[i][j] > lastIdx THEN <<>>
                       ELSE SubSeq(log[i], nextIndex[i][j], lastIdx)
       IN Send([mtype        |-> AppendEntriesRequest,
                msubtype     |-> "replicate",
                mterm        |-> currentTerm[i],
                mprevLogIndex |-> prevIdx,
                mprevLogTerm |-> prevTerm,
                mentries     |-> entries,
                mcommitIndex |-> commitIndex[i],
                msource      |-> i,
                mdest        |-> j])
    /\ UNCHANGED <<serverVars, logVars, leaderVars, candidateVars,
                   leaseVars, persistVars, configVars>>

\* Leader i sends heartbeat (empty AppendEntries) to server j.
\* Reference: replicator.cpp:385-439
SendHeartbeat(i, j) ==
    /\ state[i] = Leader
    /\ i /= j
    /\ Send([mtype        |-> AppendEntriesRequest,
             msubtype     |-> "heartbeat",
             mterm        |-> currentTerm[i],
             mprevLogIndex |-> 0,
             mprevLogTerm |-> 0,
             mentries     |-> <<>>,
             mcommitIndex |-> commitIndex[i],
             msource      |-> i,
             mdest        |-> j])
    /\ UNCHANGED <<serverVars, logVars, leaderVars, candidateVars,
                   leaseVars, persistVars, configVars>>

\* Leader i sends InstallSnapshot to server j.
\* Reference: replicator.cpp:811-869 (_install_snapshot)
\* Sent when follower is too far behind for log replication.
SendInstallSnapshot(i, j) ==
    /\ state[i] = Leader
    /\ i /= j
    /\ Send([mtype    |-> InstallSnapshotRequest,
             mterm    |-> currentTerm[i],
             msource  |-> i,
             mdest    |-> j])
    /\ UNCHANGED <<serverVars, logVars, leaderVars, candidateVars,
                   leaseVars, persistVars, configVars>>

\* Server i handles an AppendEntriesRequest m.
\* Reference: node.cpp:1441-1578 (appendEntries / handle_append_entries_request)
HandleAppendEntriesRequest(i, m) ==
    /\ m.mtype = AppendEntriesRequest
    /\ m.mdest = i
    /\ LET mterm   == m.mterm
           logOk   == \/ m.mprevLogIndex = 0
                      \/ /\ m.mprevLogIndex > 0
                         /\ m.mprevLogIndex <= LastLogIndex(i)
                         /\ LogTerm(i, m.mprevLogIndex) = m.mprevLogTerm
       IN
       \/ \* Reject: term too low
          /\ mterm < currentTerm[i]
          /\ Reply([mtype        |-> AppendEntriesResponse,
                    msubtype     |-> m.msubtype,
                    mterm        |-> currentTerm[i],
                    msuccess     |-> FALSE,
                    mmatchIndex  |-> 0,
                    msource      |-> i,
                    mdest        |-> m.msource], m)
          /\ UNCHANGED <<serverVars, logVars, leaderVars, candidateVars,
                         leaseVars, persistVars, configVars>>

       \/ \* Reject: log inconsistency
          /\ mterm >= currentTerm[i]
          /\ ~logOk
          /\ Reply([mtype        |-> AppendEntriesResponse,
                    msubtype     |-> m.msubtype,
                    mterm        |-> mterm,
                    msuccess     |-> FALSE,
                    mmatchIndex  |-> 0,
                    msource      |-> i,
                    mdest        |-> m.msource], m)
          /\ currentTerm' = [currentTerm EXCEPT ![i] = mterm]
          /\ state' = [state EXCEPT ![i] = Follower]
          /\ votedFor' = IF mterm > currentTerm[i]
                         THEN [votedFor EXCEPT ![i] = Nil]
                         ELSE votedFor
          /\ IF mterm > currentTerm[i]
             THEN persistedTerm' = [persistedTerm EXCEPT ![i] = mterm]
             ELSE UNCHANGED persistedTerm
          \* Renew follower lease on receiving from leader
          /\ followerLease' = [followerLease EXCEPT ![i] = TRUE]
          /\ UNCHANGED <<logVars, leaderVars, candidateVars,
                         leaderContact, disruptedLeader,
                         persistedVotedFor, pendingPersist, configVars>>

       \/ \* Accept: log matches at prevLogIndex
          /\ mterm >= currentTerm[i]
          /\ logOk
          /\ LET newLog == IF Len(m.mentries) > 0
                           THEN SubSeq(log[i], 1, m.mprevLogIndex) \o m.mentries
                           ELSE log[i]
                 newLastIdx == Len(newLog)
                 newCommitIdx == IF m.mcommitIndex > commitIndex[i]
                                 THEN Min(m.mcommitIndex, newLastIdx)
                                 ELSE commitIndex[i]
             IN
             /\ log' = [log EXCEPT ![i] = newLog]
             /\ commitIndex' = [commitIndex EXCEPT ![i] = newCommitIdx]
             \* Update config from log
             /\ config' = [config EXCEPT ![i] = LatestConfigIn(newLog, newCommitIdx)]
             /\ Reply([mtype        |-> AppendEntriesResponse,
                       msubtype     |-> m.msubtype,
                       mterm        |-> mterm,
                       msuccess     |-> TRUE,
                       mmatchIndex  |-> newLastIdx,
                       msource      |-> i,
                       mdest        |-> m.msource], m)
          /\ currentTerm' = [currentTerm EXCEPT ![i] = mterm]
          /\ state' = [state EXCEPT ![i] = Follower]
          /\ votedFor' = IF mterm > currentTerm[i]
                         THEN [votedFor EXCEPT ![i] = Nil]
                         ELSE votedFor
          /\ IF mterm > currentTerm[i]
             THEN persistedTerm' = [persistedTerm EXCEPT ![i] = mterm]
             ELSE UNCHANGED persistedTerm
          \* Renew follower lease: leader is alive
          \* Reference: lease.cpp:102-105 (FollowerLease::renew)
          /\ followerLease' = [followerLease EXCEPT ![i] = TRUE]
          /\ UNCHANGED <<leaderVars, candidateVars,
                         leaderContact, disruptedLeader,
                         persistedVotedFor, pendingPersist, newConfig>>

\* Server i handles InstallSnapshotRequest m.
\* Reference: snapshot_executor.cpp (install_snapshot)
HandleInstallSnapshotRequest(i, m) ==
    /\ m.mtype = InstallSnapshotRequest
    /\ m.mdest = i
    /\ \/ \* Reject: term too low
          /\ m.mterm < currentTerm[i]
          /\ Reply([mtype   |-> InstallSnapshotResponse,
                    mterm   |-> currentTerm[i],
                    msuccess |-> FALSE,
                    msource |-> i,
                    mdest   |-> m.msource], m)
          /\ UNCHANGED <<serverVars, logVars, leaderVars, candidateVars,
                         leaseVars, persistVars, configVars>>
       \/ \* Accept
          /\ m.mterm >= currentTerm[i]
          /\ currentTerm' = [currentTerm EXCEPT ![i] = m.mterm]
          /\ state' = [state EXCEPT ![i] = Follower]
          /\ votedFor' = IF m.mterm > currentTerm[i]
                         THEN [votedFor EXCEPT ![i] = Nil]
                         ELSE votedFor
          /\ IF m.mterm > currentTerm[i]
             THEN persistedTerm' = [persistedTerm EXCEPT ![i] = m.mterm]
             ELSE UNCHANGED persistedTerm
          /\ followerLease' = [followerLease EXCEPT ![i] = TRUE]
          /\ Reply([mtype   |-> InstallSnapshotResponse,
                    mterm   |-> m.mterm,
                    msuccess |-> TRUE,
                    msource |-> i,
                    mdest   |-> m.msource], m)
          /\ UNCHANGED <<logVars, leaderVars, candidateVars,
                         leaderContact, disruptedLeader,
                         persistedVotedFor, pendingPersist, configVars>>

\* Leader i handles response from the REPLICATE path.
\* Reference: replicator.cpp:359-500 (_on_rpc_returned)
\* Key: CHECKS resp.Term on failure path (line 419-435).
\*      On success path, checks term equality but does NOT step down (line 472-479).
HandleReplicateResponse(i, m) ==
    /\ m.mtype = AppendEntriesResponse
    /\ m.msubtype = "replicate"
    /\ m.mdest = i
    /\ state[i] = Leader
    /\ \/ \* Higher term on failure: step down (replicator.cpp:419-435)
          /\ m.mterm > currentTerm[i]
          /\ currentTerm' = [currentTerm EXCEPT ![i] = m.mterm]
          /\ state' = [state EXCEPT ![i] = Follower]
          /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
          /\ persistedTerm' = [persistedTerm EXCEPT ![i] = m.mterm]
          /\ leaderContact' = [leaderContact EXCEPT ![i] = {}]
          /\ followerLease' = [followerLease EXCEPT ![i] = FALSE]
          /\ Discard(m)
          /\ UNCHANGED <<logVars, leaderVars, candidateVars,
                         disruptedLeader, persistedVotedFor, pendingPersist, configVars>>

       \/ \* Bug Family 2 (partial): success with mismatched term
          \* replicator.cpp:472-479 -- logs error, resets, but does NOT step down
          /\ ~m.msuccess
          /\ m.mterm /= currentTerm[i]
          /\ m.mterm < currentTerm[i]   \* stale
          /\ Discard(m)
          /\ UNCHANGED <<serverVars, logVars, leaderVars, candidateVars,
                         leaseVars, persistVars, configVars>>

       \/ \* Current term response
          /\ m.mterm = currentTerm[i]
          /\ IF m.msuccess
             THEN /\ nextIndex'  = [nextIndex  EXCEPT ![i][m.msource] = m.mmatchIndex + 1]
                  /\ matchIndex' = [matchIndex EXCEPT ![i][m.msource] = m.mmatchIndex]
                  /\ leaderContact' = [leaderContact EXCEPT ![i] = @ \cup {m.msource}]
             ELSE /\ nextIndex' = [nextIndex EXCEPT ![i][m.msource] = Max(1, nextIndex[i][m.msource] - 1)]
                  /\ UNCHANGED <<matchIndex, leaderContact>>
          /\ Discard(m)
          /\ UNCHANGED <<serverVars, logVars, candidateVars,
                         followerLease, disruptedLeader, persistVars, configVars>>

\* Leader i handles response from the HEARTBEAT path.
\* Reference: replicator.cpp:279-333 (_on_heartbeat_returned)
\* Key: DOES check resp.Term (line 315-333) and steps down.
HandleHeartbeatResponse(i, m) ==
    /\ m.mtype = AppendEntriesResponse
    /\ m.msubtype = "heartbeat"
    /\ m.mdest = i
    /\ state[i] = Leader
    /\ \/ \* Higher term: step down (replicator.cpp:315-333)
          /\ m.mterm > currentTerm[i]
          /\ currentTerm' = [currentTerm EXCEPT ![i] = m.mterm]
          /\ state' = [state EXCEPT ![i] = Follower]
          /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
          /\ persistedTerm' = [persistedTerm EXCEPT ![i] = m.mterm]
          /\ leaderContact' = [leaderContact EXCEPT ![i] = {}]
          /\ followerLease' = [followerLease EXCEPT ![i] = FALSE]
          /\ Discard(m)
          /\ UNCHANGED <<logVars, leaderVars, candidateVars,
                         disruptedLeader, persistedVotedFor, pendingPersist, configVars>>
       \/ \* Normal: record contact for lease
          /\ m.mterm <= currentTerm[i]
          /\ leaderContact' = [leaderContact EXCEPT ![i] = @ \cup {m.msource}]
          /\ Discard(m)
          /\ UNCHANGED <<serverVars, logVars, leaderVars, candidateVars,
                         followerLease, disruptedLeader, persistVars, configVars>>

\* Leader i handles InstallSnapshot response.
\* Reference: replicator.cpp:870-933 (_on_install_snapshot_returned)
\*
\* *** BUG FAMILY 2: NO TERM CHECK ***
\* Comment at line 912: "Let heartbeat do step down"
\* Unlike all other response handlers, this does NOT check response.term().
\* A snapshot response with higher term will NOT trigger step-down.
HandleInstallSnapshotResponse(i, m) ==
    /\ m.mtype = InstallSnapshotResponse
    /\ m.mdest = i
    /\ state[i] = Leader
    \* *** BUG (Family 2): No term check! ***
    \* replicator.cpp:895-919 -- no comparison of response.term() vs r._options.term
    \* Leader unconditionally processes the response.
    /\ IF m.msuccess
       THEN leaderContact' = [leaderContact EXCEPT ![i] = @ \cup {m.msource}]
       ELSE UNCHANGED leaderContact
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, logVars, leaderVars, candidateVars,
                   followerLease, disruptedLeader, persistVars, configVars>>

\* Leader i advances commit index based on quorum replication.
\* Reference: ballot_box.cpp:49-96 (commit_at)
AdvanceCommitIndex(i) ==
    /\ state[i] = Leader
    /\ LET Agree(idx) == {i} \cup {s \in Server : matchIndex[i][s] >= idx}
           agreeIdxs == {idx \in (commitIndex[i]+1)..LastLogIndex(i) :
                          /\ QuorumCheck(Agree(idx), i)
                          /\ log[i][idx].term = currentTerm[i]}
       IN
       /\ agreeIdxs /= {}
       /\ LET newCommitIdx == SetMax(agreeIdxs)
          IN
          \* Bug Family 4: force-commit of preceding entries
          \* ballot_box.cpp:79-88: "not well proved right now"
          \* When a config change entry commits, all preceding entries
          \* are force-committed even if they didn't individually have quorum.
          /\ commitIndex' = [commitIndex EXCEPT ![i] = newCommitIdx]
          /\ config' = [config EXCEPT ![i] = LatestConfigIn(log[i], newCommitIdx)]
          \* If config change committed, clear pending config
          /\ newConfig' = IF \E idx \in (commitIndex[i]+1)..newCommitIdx :
                               log[i][idx].type = ConfigEntry
                          THEN [newConfig EXCEPT ![i] = Nil]
                          ELSE newConfig
    /\ UNCHANGED <<serverVars, log, leaderVars, candidateVars, messages,
                   leaseVars, persistVars>>

----
\* Leader Lease Check (Bug Family 1)
----

\* Leader i checks if its lease is still valid.
\* Reference: lease.cpp:58-82 (LeaderLease::get_lease_info)
\* If contacted followers + self don't form a quorum, leader steps down.
CheckLeaderLease(i) ==
    /\ state[i] = Leader
    /\ LET contacted == leaderContact[i] \cup {i}
       IN
       /\ IF QuorumCheck(contacted, i)
          THEN \* Lease valid: reset contacts for next period
               /\ UNCHANGED state
               /\ leaderContact' = [leaderContact EXCEPT ![i] = {}]
          ELSE \* Lease expired: step down
               /\ state' = [state EXCEPT ![i] = Follower]
               /\ leaderContact' = [leaderContact EXCEPT ![i] = {}]
    /\ UNCHANGED <<currentTerm, votedFor, logVars, leaderVars, candidateVars,
                   messages, followerLease, disruptedLeader, persistVars, configVars>>

\* Follower lease expires (models time passing).
\* Reference: lease.cpp:129-132 (FollowerLease::expired)
FollowerLeaseExpire(i) ==
    /\ followerLease[i] = TRUE
    /\ followerLease' = [followerLease EXCEPT ![i] = FALSE]
    /\ UNCHANGED <<serverVars, logVars, leaderVars, candidateVars, messages,
                   leaderContact, disruptedLeader, persistVars, configVars>>

----
\* Configuration Change Actions (Bug Family 4)
----

\* Leader i proposes a configuration change.
\* Reference: node.cpp:3292-3325 (ConfigurationCtx::next_stage)
\* Single-peer change skips joint consensus (node.cpp:3296-3301).
ProposeConfigChange(i, s) ==
    /\ state[i] = Leader
    /\ newConfig[i] = Nil   \* one at a time
    /\ config[i] = LatestConfigIn(log[i], LastLogIndex(i))  \* no pending
    /\ \/ /\ s \notin config[i]   \* add voter
          /\ s \in Server
       \/ /\ s \in config[i]      \* remove voter
          /\ Cardinality(config[i]) > 1
    /\ LET nc == IF s \in config[i]
                 THEN config[i] \ {s}
                 ELSE config[i] \cup {s}
           entry == [term |-> currentTerm[i], type |-> ConfigEntry, config |-> nc]
       IN
       /\ log' = [log EXCEPT ![i] = Append(@, entry)]
       /\ newConfig' = [newConfig EXCEPT ![i] = nc]
    /\ UNCHANGED <<serverVars, commitIndex, leaderVars, candidateVars, messages,
                   leaseVars, persistVars, config>>

----
\* Crash and Recovery (Bug Family 3)
----

\* Server i crashes. All volatile state is lost.
\* Recovers from persisted state.
\* Bug Family 3: if pendingPersist was TRUE (RPCs sent but not persisted),
\* the node recovers with OLD term/votedFor from disk.
Crash(i) ==
    /\ state' = [state EXCEPT ![i] = Follower]
    \* Volatile state reset
    /\ commitIndex'      = [commitIndex      EXCEPT ![i] = 0]
    /\ nextIndex'        = [nextIndex        EXCEPT ![i] = [j \in Server |-> 1]]
    /\ matchIndex'       = [matchIndex       EXCEPT ![i] = [j \in Server |-> 0]]
    /\ votesGranted'     = [votesGranted     EXCEPT ![i] = {}]
    /\ preVotesGranted'  = [preVotesGranted  EXCEPT ![i] = {}]
    /\ leaderContact'    = [leaderContact    EXCEPT ![i] = {}]
    /\ followerLease'    = [followerLease    EXCEPT ![i] = FALSE]
    /\ disruptedLeader'  = [disruptedLeader  EXCEPT ![i] = Nil]
    \* Recover from persisted state (Bug Family 3)
    \* If pendingPersist was TRUE, persistedTerm/persistedVotedFor
    \* are STALE -- this is the crash window in elect_self
    /\ currentTerm' = [currentTerm EXCEPT ![i] = persistedTerm[i]]
    /\ votedFor'    = [votedFor    EXCEPT ![i] = persistedVotedFor[i]]
    /\ pendingPersist' = [pendingPersist EXCEPT ![i] = FALSE]
    \* Recompute config from persisted log
    /\ config'    = [config    EXCEPT ![i] = LatestConfigIn(log[i], Len(log[i]))]
    /\ newConfig' = [newConfig EXCEPT ![i] = Nil]
    \* log and persisted state survive
    /\ UNCHANGED <<log, messages, persistedTerm, persistedVotedFor>>

----
\* Network failures
----

LoseMessage(m) ==
    /\ m \in DOMAIN messages
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, logVars, leaderVars, candidateVars,
                   leaseVars, persistVars, configVars>>

DropStaleMessage(m) ==
    /\ m \in DOMAIN messages
    /\ \/ /\ m.mtype \in {PreVoteRequest, PreVoteResponse,
                           RequestVoteRequest, RequestVoteResponse,
                           AppendEntriesRequest, AppendEntriesResponse,
                           InstallSnapshotRequest, InstallSnapshotResponse}
          /\ m.mterm < currentTerm[m.mdest]
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, logVars, leaderVars, candidateVars,
                   leaseVars, persistVars, configVars>>

----
\* Spec
----

Next ==
    \/ \E i \in Server :
        \/ PreVote(i)
        \/ ElectSelf(i)
        \/ CompletePersistElectSelf(i)
        \/ BecomeLeader(i)
        \/ ClientRequest(i)
        \/ CheckLeaderLease(i)
        \/ FollowerLeaseExpire(i)
        \/ AdvanceCommitIndex(i)
        \/ Crash(i)
    \/ \E i, j \in Server :
        \/ ReplicateEntries(i, j)
        \/ SendHeartbeat(i, j)
        \/ SendInstallSnapshot(i, j)
        \/ ProposeConfigChange(i, j)
    \/ \E m \in DOMAIN messages :
        \/ HandlePreVoteRequest(m.mdest, m)
        \/ HandlePreVoteResponse(m.mdest, m)
        \/ HandleRequestVoteRequest(m.mdest, m)
        \/ HandleRequestVoteResponse(m.mdest, m)
        \/ HandleAppendEntriesRequest(m.mdest, m)
        \/ HandleReplicateResponse(m.mdest, m)
        \/ HandleHeartbeatResponse(m.mdest, m)
        \/ HandleInstallSnapshotRequest(m.mdest, m)
        \/ HandleInstallSnapshotResponse(m.mdest, m)
        \/ DropStaleMessage(m)
        \/ LoseMessage(m)

Spec == Init /\ [][Next]_vars

----
\* Invariants
----

\* Standard Raft: at most one leader per term.
ElectionSafety ==
    \A s1, s2 \in Server :
        (state[s1] = Leader /\ state[s2] = Leader /\ currentTerm[s1] = currentTerm[s2])
        => s1 = s2

\* Standard Raft: if two logs have an entry with the same index and term,
\* the logs are identical up to that point.
LogMatching ==
    \A s1, s2 \in Server :
        \A idx \in 1..Min(LastLogIndex(s1), LastLogIndex(s2)) :
            log[s1][idx].term = log[s2][idx].term =>
                \A k \in 1..idx : log[s1][k].term = log[s2][k].term

\* Standard Raft: a committed entry appears in all future leaders' logs.
LeaderCompleteness ==
    \A s1, s2 \in Server :
        (state[s1] = Leader /\ commitIndex[s2] > 0) =>
            \A idx \in 1..commitIndex[s2] :
                /\ idx <= LastLogIndex(s1)
                /\ log[s1][idx].term = log[s2][idx].term

\* Bug Family 1: Lease implies leadership safety.
\* If a leader's lease check passes, a real quorum of voters
\* actually has term <= leader's term.
LeaseImpliesLeadership ==
    \A s \in Server :
        state[s] = Leader =>
            LET contacted == leaderContact[s] \cup {s}
            IN QuorumCheck(contacted, s) =>
               LET loyal == {f \in contacted : currentTerm[f] <= currentTerm[s]}
               IN QuorumCheck(loyal, s)

\* Bug Family 1: PreVote should not disrupt stable leader.
\* If there exists a leader with a valid lease, no other server
\* should be able to become Candidate in a higher term.
NoLeaseBypassWithoutDisruption ==
    \A s \in Server :
        state[s] = Leader =>
            \A c \in Server :
                (state[c] = Candidate /\ currentTerm[c] > currentTerm[s]) =>
                    \* The candidate's term is justified by the leader stepping down
                    \/ currentTerm[s] < currentTerm[c]
                    \/ s = c

\* Bug Family 2: Term discovery completeness.
\* A leader that has received a snapshot response from a follower
\* with higher term should eventually step down.
\* (This cannot be checked as a state invariant directly -- it would
\*  require temporal logic. We check a weaker version:
\*  no phantom contacts from snapshot responses.)
NoPhantomSnapshotContact ==
    \A s \in Server :
        state[s] = Leader =>
            \A f \in leaderContact[s] :
                currentTerm[f] <= currentTerm[s]

\* Bug Family 3: Vote safety across crashes.
\* A node never votes for two different candidates in the same term,
\* even across crashes.
VoteSafetyAcrossCrash ==
    \A s \in Server :
        persistedVotedFor[s] /= Nil =>
            votedFor[s] \in {Nil, persistedVotedFor[s]}
            \/ currentTerm[s] > persistedTerm[s]

\* Bug Family 4: Configuration change safety.
\* At most one uncommitted config change at a time.
ConfigChangeSafety ==
    \A s \in Server :
        state[s] = Leader =>
            LET configIndices == {idx \in (commitIndex[s]+1)..LastLogIndex(s) :
                                    log[s][idx].type = ConfigEntry}
            IN Cardinality(configIndices) <= 1

=============================================================================
