--------------------------- MODULE Trace ---------------------------
\* Trace validation spec for brpc/braft.
\*
\* Reads an NDJSON trace file produced by the instrumentation harness,
\* and replays each event against the base spec to verify
\* the implementation matches the specification.

EXTENDS base, Json, IOUtils, Sequences, TLC

----
\* Trace loading
----

JsonFile ==
    IF "JSON" \in DOMAIN IOEnv THEN IOEnv.JSON
    ELSE "../traces/trace.ndjson"

TraceLog == TLCEval(
    LET all == ndJsonDeserialize(JsonFile)
    IN SelectSeq(all, LAMBDA x :
        /\ "tag" \in DOMAIN x
        /\ x.tag = "trace"
        /\ "event" \in DOMAIN x))

ASSUME Len(TraceLog) > 0

----
\* Trace cursor
----

VARIABLE l       \* Current position in TraceLog (1-indexed)

traceVars == <<l>>

logline == TraceLog[l]

----
\* Role mapping
----

RaftRole ==
    "Follower"  :> Follower  @@
    "Candidate" :> Candidate @@
    "Leader"    :> Leader

----
\* Server extraction from trace
----

TraceServer == TLCEval(
    UNION {
        {TraceLog[k].event.nid}
        \cup (IF "msg" \in DOMAIN TraceLog[k].event
              THEN {TraceLog[k].event.msg.from, TraceLog[k].event.msg.to}
                    \ {""}
              ELSE {})
        : k \in 1..Len(TraceLog)
    })

ASSUME TraceServer /= {}
ASSUME TraceServer \subseteq Server

----
\* Bootstrap state
\*
\* braft initializes with term=1 and empty log.
\* (node.cpp:437-438: if _current_term == 0 then _current_term = 1)
----

TraceInit ==
    /\ l = 1
    /\ currentTerm      = [s \in Server |-> 1]
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
    /\ persistedTerm     = [s \in Server |-> 1]
    /\ persistedVotedFor = [s \in Server |-> Nil]
    /\ pendingPersist    = [s \in Server |-> FALSE]
    /\ config            = [s \in Server |-> Server]
    /\ newConfig         = [s \in Server |-> Nil]

----
\* Event predicates
----

IsEvent(name) ==
    /\ l <= Len(TraceLog)
    /\ logline.event.name = name

IsNodeEvent(name, i) ==
    /\ IsEvent(name)
    /\ logline.event.nid = i

IsMsgEvent(name, from, to) ==
    /\ IsEvent(name)
    /\ "msg" \in DOMAIN logline.event
    /\ logline.event.msg.from = from
    /\ logline.event.msg.to = to

----
\* Post-state validation
\*
\* Full: validates term, role, commitIndex, lastLogIndex, lastLogTerm.
\* Use for node.cpp events that capture(this) AFTER state change.
\*
\* Weak: validates only term and role.
\* Use for replicator.cpp events (capture_weak) or events where
\* the trace captures state before log/commitIndex updates.
\*
\* Commit: validates term, role, and commitIndex.
\* Use for AdvanceCommitIndex (capture_weak + manual commitIndex).
----

ValidatePostState(i) ==
    /\ currentTerm'[i] = logline.event.state.term
    /\ state'[i] = RaftRole[logline.event.state.role]
    /\ commitIndex'[i] = logline.event.state.commitIndex
    /\ LastLogIndex(i)' = logline.event.state.lastLogIndex
    /\ LastLogTerm(i)' = logline.event.state.lastLogTerm

ValidatePostStateWeak(i) ==
    /\ currentTerm'[i] = logline.event.state.term
    /\ state'[i] = RaftRole[logline.event.state.role]

ValidatePostStateCommit(i) ==
    /\ currentTerm'[i] = logline.event.state.term
    /\ state'[i] = RaftRole[logline.event.state.role]
    /\ commitIndex'[i] = logline.event.state.commitIndex

TraceVotedFor(i) ==
    LET v == logline.event.state.votedFor
    IN IF v = "" THEN Nil ELSE v

ValidateVotedFor(i) ==
    votedFor'[i] = TraceVotedFor(i)

----
\* Step trace cursor
----

StepTrace == l' = l + 1

----
\* Silent actions (no trace event consumed)
----

\* Concurrent PreVote: when multiple nodes pre-vote simultaneously,
\* the trace may serialize events non-causally.
\* Also handles untraced pre-vote phase before BecomeCandidate.
SilentPreVote ==
    /\ l <= Len(TraceLog)
    /\ logline.event.name \in {"HandlePreVoteRequest", "BecomeCandidate"}
    /\ \E i \in Server :
        /\ \/ /\ logline.event.name = "HandlePreVoteRequest"
              /\ "msg" \in DOMAIN logline.event
              /\ i = logline.event.msg.from
           \/ /\ logline.event.name = "BecomeCandidate"
              /\ i = logline.event.nid
        /\ state[i] = Follower
        /\ preVotesGranted[i] = {}  \* Not yet pre-voted
        /\ PreVote(i)
        /\ UNCHANGED l

\* Concurrent timeout: fires ElectSelf without consuming trace event.
SilentElectSelf ==
    /\ l <= Len(TraceLog)
    /\ logline.event.name = "HandleRequestVoteRequest"
    /\ "msg" \in DOMAIN logline.event
    /\ \E i \in Server :
        /\ i = logline.event.msg.from
        /\ state[i] = Follower
        /\ ElectSelf(i)
        /\ UNCHANGED l

\* Leader appends entry (noop or client request) without trace event.
FillLogGap ==
    /\ l <= Len(TraceLog)
    /\ LET nid     == logline.event.nid
           expected == logline.event.state.lastLogIndex
       IN
       /\ state[nid] = Leader
       /\ LastLogIndex(nid) < expected
       /\ ClientRequest(nid)
       /\ UNCHANGED l

\* Complete pending persist without trace event.
SilentCompletePersist ==
    /\ l <= Len(TraceLog)
    /\ \E i \in Server :
        /\ pendingPersist[i] = TRUE
        /\ CompletePersistElectSelf(i)
        /\ UNCHANGED l

\* Follower lease expires without trace event.
SilentFollowerLeaseExpire ==
    /\ l <= Len(TraceLog)
    /\ \E i \in Server :
        /\ followerLease[i] = TRUE
        /\ FollowerLeaseExpire(i)
        /\ UNCHANGED l

\* Concurrent replicate response processing.
SilentHandleReplicateResponse ==
    /\ l <= Len(TraceLog)
    /\ logline.event.name = "AdvanceCommitIndex"
    /\ LET i == logline.event.nid
           expectedCI == logline.event.state.commitIndex
           Agree(idx) == {i} \cup {s \in Server : matchIndex[i][s] >= idx}
       IN
       /\ ~ QuorumCheck(Agree(expectedCI), i)
       /\ \E m \in DOMAIN messages :
           /\ m.mtype = AppendEntriesResponse
           /\ m.msubtype = "replicate"
           /\ m.mdest = i
           /\ HandleReplicateResponse(i, m)
           /\ UNCHANGED l

\* Leader sends heartbeat (or probe) without trace event.
\* braft's Replicator sends probes on startup that aren't traced
\* as SendHeartbeat events. This creates the message in the bag
\* so HandleAppendEntriesRequest can consume it.
SilentSendHeartbeat ==
    /\ l <= Len(TraceLog)
    /\ logline.event.name = "HandleAppendEntriesRequest"
    /\ "msg" \in DOMAIN logline.event
    /\ ~ "prevLogIndex" \in DOMAIN logline.event.msg  \* heartbeat/probe
    /\ LET from == logline.event.msg.from
           to   == logline.event.nid
       IN
       /\ ~ \E m \in DOMAIN messages :
               /\ m.mtype = AppendEntriesRequest
               /\ m.msource = from
               /\ m.mdest = to
               /\ m.msubtype = "heartbeat"
       /\ SendHeartbeat(from, to)
       /\ UNCHANGED l

\* Silent HandlePreVoteRequest: process pending pre-vote requests
\* from the message bag. Needed when the pre-vote flow isn't traced
\* (e.g., before an untraced BecomeCandidate).
SilentHandlePreVoteRequest ==
    /\ l <= Len(TraceLog)
    /\ logline.event.name = "BecomeCandidate"
    /\ \E i \in Server, m \in DOMAIN messages :
        /\ m.mtype = PreVoteRequest
        /\ m.mdest = i
        /\ HandlePreVoteRequest(i, m)
        /\ UNCHANGED l

\* Silent HandlePreVoteResponse: process pending pre-vote responses
\* from the message bag. Needed when the pre-vote flow isn't traced.
SilentHandlePreVoteResponse ==
    /\ l <= Len(TraceLog)
    /\ logline.event.name = "BecomeCandidate"
    /\ \E i \in Server, m \in DOMAIN messages :
        /\ m.mtype = PreVoteResponse
        /\ m.mdest = i
        /\ HandlePreVoteResponse(i, m)
        /\ UNCHANGED l

----
\* Action wrappers
----

\* PreVote -> PreVote(i)
PreVoteIfLogged ==
    \E i \in Server :
        /\ IsNodeEvent("PreVote", i)
        /\ \/ /\ PreVote(i)
              /\ ValidatePostStateWeak(i)
              /\ StepTrace
           \/ \* Already pre-voted via SilentPreVote
              /\ preVotesGranted[i] /= {}
              /\ UNCHANGED vars
              /\ StepTrace

\* HandlePreVoteRequest -> HandlePreVoteRequest(i, m)
HandlePreVoteRequestIfLogged ==
    \E i \in Server :
        /\ IsEvent("HandlePreVoteRequest")
        /\ logline.event.nid = i
        /\ "msg" \in DOMAIN logline.event
        /\ \E m \in DOMAIN messages :
            /\ m.mtype = PreVoteRequest
            /\ m.msource = logline.event.msg.from
            /\ m.mdest = i
            /\ HandlePreVoteRequest(i, m)
            /\ ValidatePostStateWeak(i)
            /\ StepTrace

\* HandlePreVoteResponse -> HandlePreVoteResponse(i, m)
HandlePreVoteResponseIfLogged ==
    \E i \in Server :
        /\ IsEvent("HandlePreVoteResponse")
        /\ logline.event.nid = i
        /\ "msg" \in DOMAIN logline.event
        /\ \/ \E m \in DOMAIN messages :
                /\ m.mtype = PreVoteResponse
                /\ m.msource = logline.event.msg.from
                /\ m.mdest = i
                /\ HandlePreVoteResponse(i, m)
                /\ ValidatePostStateWeak(i)
                /\ StepTrace
           \/ \* Transport failure
              /\ ~ \E m \in DOMAIN messages :
                      /\ m.mtype = PreVoteResponse
                      /\ m.msource = logline.event.msg.from
                      /\ m.mdest = i
              /\ UNCHANGED vars
              /\ StepTrace

\* ElectSelf (BecomeCandidate) -> ElectSelf(i)
ElectSelfIfLogged ==
    \E i \in Server :
        /\ IsNodeEvent("BecomeCandidate", i)
        /\ \/ /\ ElectSelf(i)
              /\ ValidatePostState(i)
              /\ ValidateVotedFor(i)
              /\ StepTrace
           \/ \* Already elected via SilentElectSelf
              /\ state[i] = Candidate
              /\ currentTerm[i] = logline.event.state.term
              /\ votedFor[i] = TraceVotedFor(i)
              /\ UNCHANGED vars
              /\ StepTrace

\* HandleRequestVoteRequest -> HandleRequestVoteRequest(i, m)
HandleRequestVoteRequestIfLogged ==
    \E i \in Server :
        /\ IsEvent("HandleRequestVoteRequest")
        /\ logline.event.nid = i
        /\ "msg" \in DOMAIN logline.event
        /\ \E m \in DOMAIN messages :
            /\ m.mtype = RequestVoteRequest
            /\ m.msource = logline.event.msg.from
            /\ m.mdest = i
            /\ HandleRequestVoteRequest(i, m)
            /\ ValidatePostState(i)
            /\ StepTrace

\* HandleRequestVoteResponse -> HandleRequestVoteResponse(i, m)
HandleRequestVoteResponseIfLogged ==
    \E i \in Server :
        /\ IsEvent("HandleRequestVoteResponse")
        /\ logline.event.nid = i
        /\ "msg" \in DOMAIN logline.event
        /\ \/ \* Self-vote: skip
              /\ logline.event.msg.from = logline.event.msg.to
              /\ logline.event.msg.from = i
              /\ UNCHANGED vars
              /\ StepTrace
           \/ \* Remote vote
              /\ logline.event.msg.from /= logline.event.msg.to
              /\ \/ \E m \in DOMAIN messages :
                       /\ m.mtype = RequestVoteResponse
                       /\ m.msource = logline.event.msg.from
                       /\ m.mdest = i
                       /\ \/ /\ HandleRequestVoteResponse(i, m)
                             /\ ValidatePostState(i)
                             /\ StepTrace
                          \/ /\ DropStaleMessage(m)
                             /\ StepTrace
                 \/ \* Transport failure
                    /\ ~ \E m \in DOMAIN messages :
                            /\ m.mtype = RequestVoteResponse
                            /\ m.msource = logline.event.msg.from
                            /\ m.mdest = i
                    /\ UNCHANGED vars
                    /\ StepTrace

\* BecomeLeader -> BecomeLeader(i)
BecomeLeaderIfLogged ==
    \E i \in Server :
        /\ IsNodeEvent("BecomeLeader", i)
        /\ BecomeLeader(i)
        /\ ValidatePostState(i)
        /\ StepTrace

\* SendReplicateEntries -> ReplicateEntries(i, j)
\* Uses ValidatePostStateWeak because replicator.cpp uses capture_weak.
ReplicateEntriesIfLogged ==
    \E i \in Server :
        /\ IsEvent("SendReplicateEntries")
        /\ logline.event.nid = i
        /\ "msg" \in DOMAIN logline.event
        /\ LET j == logline.event.msg.to IN
            /\ j \in Server
            /\ ReplicateEntries(i, j)
            /\ ValidatePostStateWeak(i)
            /\ StepTrace

\* SendHeartbeat -> SendHeartbeat(i, j)
SendHeartbeatIfLogged ==
    \E i \in Server :
        /\ IsEvent("SendHeartbeat")
        /\ logline.event.nid = i
        /\ "msg" \in DOMAIN logline.event
        /\ LET j == logline.event.msg.to IN
            /\ j \in Server
            /\ SendHeartbeat(i, j)
            /\ ValidatePostStateWeak(i)
            /\ StepTrace

\* SendInstallSnapshot -> SendInstallSnapshot(i, j)
SendInstallSnapshotIfLogged ==
    \E i \in Server :
        /\ IsEvent("SendInstallSnapshot")
        /\ logline.event.nid = i
        /\ "msg" \in DOMAIN logline.event
        /\ LET j == logline.event.msg.to IN
            /\ j \in Server
            /\ SendInstallSnapshot(i, j)
            /\ ValidatePostStateWeak(i)
            /\ StepTrace

\* HandleAppendEntriesRequest -> HandleAppendEntriesRequest(i, m)
\* Uses ValidatePostStateWeak because the trace captures state BEFORE
\* log/commitIndex updates (trace at line 2620/2675, updates at 2631/2687).
HandleAppendEntriesRequestIfLogged ==
    \E i \in Server :
        /\ IsEvent("HandleAppendEntriesRequest")
        /\ logline.event.nid = i
        /\ "msg" \in DOMAIN logline.event
        /\ \E m \in DOMAIN messages :
            /\ m.mtype = AppendEntriesRequest
            /\ m.msource = logline.event.msg.from
            /\ m.mdest = i
            /\ m.mterm = logline.event.msg.term
            /\ IF "prevLogIndex" \in DOMAIN logline.event.msg
               THEN m.msubtype = "replicate"
               ELSE m.msubtype = "heartbeat"
            /\ HandleAppendEntriesRequest(i, m)
            /\ ValidatePostStateWeak(i)
            /\ StepTrace

\* HandleReplicateResponse -> HandleReplicateResponse(i, m)
HandleReplicateResponseIfLogged ==
    \E i \in Server :
        /\ IsEvent("HandleReplicateResponse")
        /\ logline.event.nid = i
        /\ "msg" \in DOMAIN logline.event
        /\ \/ \E m \in DOMAIN messages :
                /\ m.mtype = AppendEntriesResponse
                /\ m.msubtype = "replicate"
                /\ m.msource = logline.event.msg.from
                /\ m.mdest = i
                /\ HandleReplicateResponse(i, m)
                /\ ValidatePostStateWeak(i)
                /\ StepTrace
           \/ \* No matching replicate response (probe response or already consumed)
              /\ ~ \E m \in DOMAIN messages :
                      /\ m.mtype = AppendEntriesResponse
                      /\ m.msubtype = "replicate"
                      /\ m.msource = logline.event.msg.from
                      /\ m.mdest = i
              /\ UNCHANGED vars
              /\ StepTrace

\* HandleHeartbeatResponse -> HandleHeartbeatResponse(i, m)
HandleHeartbeatResponseIfLogged ==
    \E i \in Server :
        /\ IsEvent("HandleHeartbeatResponse")
        /\ logline.event.nid = i
        /\ "msg" \in DOMAIN logline.event
        /\ \E m \in DOMAIN messages :
            /\ m.mtype = AppendEntriesResponse
            /\ m.msubtype = "heartbeat"
            /\ m.msource = logline.event.msg.from
            /\ m.mdest = i
            /\ HandleHeartbeatResponse(i, m)
            /\ ValidatePostStateWeak(i)
            /\ StepTrace

\* HandleInstallSnapshotRequest -> HandleInstallSnapshotRequest(i, m)
HandleInstallSnapshotRequestIfLogged ==
    \E i \in Server :
        /\ IsEvent("HandleInstallSnapshotRequest")
        /\ logline.event.nid = i
        /\ "msg" \in DOMAIN logline.event
        /\ \E m \in DOMAIN messages :
            /\ m.mtype = InstallSnapshotRequest
            /\ m.msource = logline.event.msg.from
            /\ m.mdest = i
            /\ HandleInstallSnapshotRequest(i, m)
            /\ ValidatePostState(i)
            /\ StepTrace

\* HandleInstallSnapshotResponse -> HandleInstallSnapshotResponse(i, m)
HandleInstallSnapshotResponseIfLogged ==
    \E i \in Server :
        /\ IsEvent("HandleInstallSnapshotResponse")
        /\ logline.event.nid = i
        /\ "msg" \in DOMAIN logline.event
        /\ \E m \in DOMAIN messages :
            /\ m.mtype = InstallSnapshotResponse
            /\ m.msource = logline.event.msg.from
            /\ m.mdest = i
            /\ HandleInstallSnapshotResponse(i, m)
            /\ ValidatePostStateWeak(i)
            /\ StepTrace

\* ProposeConfigChange -> ProposeConfigChange(i, s)
ProposeConfigChangeIfLogged ==
    \E i \in Server :
        /\ IsNodeEvent("ProposeConfigChange", i)
        /\ \/ \* Actual config change (has msg.to = server to add/remove)
              /\ "msg" \in DOMAIN logline.event
              /\ LET s == logline.event.msg.to IN
                  /\ ProposeConfigChange(i, s)
                  /\ ValidatePostState(i)
                  /\ StepTrace
           \/ \* Initial config entry (no msg = leader writes current config)
              \* Log was already filled by FillLogGap; just validate and step.
              /\ "msg" \notin DOMAIN logline.event
              /\ UNCHANGED vars
              /\ ValidatePostState(i)
              /\ StepTrace

\* AdvanceCommitIndex -> AdvanceCommitIndex(i)
\* Uses ValidatePostStateCommit because ballot_box.cpp uses capture_weak
\* but manually sets commitIndex (lastLogIndex/lastLogTerm are 0).
AdvanceCommitIndexIfLogged ==
    \E i \in Server :
        /\ IsNodeEvent("AdvanceCommitIndex", i)
        /\ AdvanceCommitIndex(i)
        /\ ValidatePostStateCommit(i)
        /\ StepTrace

\* CheckLeaderLease -> CheckLeaderLease(i)
CheckLeaderLeaseIfLogged ==
    \E i \in Server :
        /\ IsNodeEvent("CheckLeaderLease", i)
        /\ CheckLeaderLease(i)
        /\ ValidatePostStateWeak(i)
        /\ StepTrace

----
\* Main transition
----

TraceNext ==
    \* Action wrappers (consume trace events)
    \/ PreVoteIfLogged
    \/ HandlePreVoteRequestIfLogged
    \/ HandlePreVoteResponseIfLogged
    \/ ElectSelfIfLogged
    \/ HandleRequestVoteRequestIfLogged
    \/ HandleRequestVoteResponseIfLogged
    \/ BecomeLeaderIfLogged
    \/ ReplicateEntriesIfLogged
    \/ SendHeartbeatIfLogged
    \/ SendInstallSnapshotIfLogged
    \/ HandleAppendEntriesRequestIfLogged
    \/ HandleReplicateResponseIfLogged
    \/ HandleHeartbeatResponseIfLogged
    \/ HandleInstallSnapshotRequestIfLogged
    \/ HandleInstallSnapshotResponseIfLogged
    \/ AdvanceCommitIndexIfLogged
    \/ ProposeConfigChangeIfLogged
    \/ CheckLeaderLeaseIfLogged
    \* Silent actions (no trace event consumed)
    \/ FillLogGap
    \/ SilentPreVote
    \/ SilentElectSelf
    \/ SilentCompletePersist
    \/ SilentFollowerLeaseExpire
    \/ SilentHandleReplicateResponse
    \/ SilentSendHeartbeat
    \/ SilentHandlePreVoteRequest
    \/ SilentHandlePreVoteResponse

----
\* Spec and properties
----

TraceSpec == TraceInit /\ [][TraceNext]_<<l, vars>> /\ WF_<<l, vars>>(TraceNext)

TraceView == <<vars, l>>

TraceMatched == <>(l > Len(TraceLog))

TraceAlias ==
    [
        l         |-> l,
        len       |-> Len(TraceLog),
        event     |-> IF l <= Len(TraceLog) THEN logline.event.name ELSE "DONE",
        nid       |-> IF l <= Len(TraceLog) THEN logline.event.nid ELSE "DONE",
        tState    |-> IF l <= Len(TraceLog) THEN logline.event.state ELSE "DONE",
        term      |-> currentTerm,
        vFor      |-> votedFor,
        role      |-> state,
        cIdx      |-> commitIndex,
        logLen    |-> [s \in Server |-> Len(log[s])],
        vGrant    |-> votesGranted,
        pvGrant   |-> preVotesGranted,
        msgCount  |-> BagCardinality(messages),
        lease     |-> leaderContact,
        fLease    |-> followerLease
    ]

=============================================================================
