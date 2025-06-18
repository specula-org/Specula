--------------------------- MODULE specTrace ---------------------------

EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags, Json, IOUtils, test, TraceSpec, TVOperators


TraceNil == "null"

(* Extract system configuration from first trace line *)
TraceNodes == ToSet(Trace[1].Nodes)
TraceMaxLogLength == ToSet(Trace[1].MaxLogLength)
TraceMaxTerm == ToSet(Trace[1].MaxTerm)

(* Default variable initialization *)
DefaultImpl(varName) ==
    CASE varName = "currentTerm" -> [n \in TraceNodes |-> 0]
     [] varName = "votedFor" -> [n \in TraceNodes |-> 0]
     [] varName = "log" -> [n \in TraceNodes |-> <<>>]
     [] varName = "commitIndex" -> [n \in TraceNodes |-> 0]
     [] varName = "state" -> [n \\in TraceNodes |-> "Follower"]
     [] varName = "leaderId" -> [n \in TraceNodes |-> 0]
     [] varName = "nextIndex" -> [n \\in TraceNodes |-> [m \\in TraceNodes |-> 1]]
     [] varName = "matchIndex" -> [n \\in TraceNodes |-> [m \\in TraceNodes |-> 0]]
     [] varName = "votes" -> [n \\in TraceNodes |-> {}]
     [] varName = "electionTimeout" -> [n \in TraceNodes |-> FALSE]
     [] varName = "messages" -> {}

(* State variable update logic *)
UpdateVariablesImpl(t) ==
    /\ IF "currentTerm" \in DOMAIN t
       THEN currentTerm' = UpdateVariable(currentTerm, "currentTerm", t)
       ELSE TRUE
    /\ IF "votedFor" \in DOMAIN t
       THEN votedFor' = UpdateVariable(votedFor, "votedFor", t)
       ELSE TRUE
    /\ IF "log" \in DOMAIN t
       THEN log' = UpdateVariable(log, "log", t)
       ELSE TRUE
    /\ IF "commitIndex" \in DOMAIN t
       THEN commitIndex' = UpdateVariable(commitIndex, "commitIndex", t)
       ELSE TRUE
    /\ IF "state" \in DOMAIN t
       THEN state' = UpdateVariable(state, "state", t)
       ELSE TRUE
    /\ IF "leaderId" \in DOMAIN t
       THEN leaderId' = UpdateVariable(leaderId, "leaderId", t)
       ELSE TRUE
    /\ IF "nextIndex" \in DOMAIN t
       THEN nextIndex' = UpdateVariable(nextIndex, "nextIndex", t)
       ELSE TRUE
    /\ IF "matchIndex" \in DOMAIN t
       THEN matchIndex' = UpdateVariable(matchIndex, "matchIndex", t)
       ELSE TRUE
    /\ IF "votes" \in DOMAIN t
       THEN votes' = UpdateVariable(votes, "votes", t)
       ELSE TRUE
    /\ IF "electionTimeout" \in DOMAIN t
       THEN electionTimeout' = UpdateVariable(electionTimeout, "electionTimeout", t)
       ELSE TRUE
    /\ IF "messages" \in DOMAIN t
       THEN messages' = UpdateVariable(messages, "messages", t)
       ELSE TRUE

(* Action event matching *)

IsBecomeCandidate ==
    /\ IsEvent("BecomeCandidate")
    /\ \E n \in TraceNodes :
        BecomeCandidate(n)

IsBecomeLeader ==
    /\ IsEvent("BecomeLeader")
    /\ \E n \in TraceNodes :
        BecomeLeader(n)

IsRequestVote ==
    /\ IsEvent("RequestVote")
    /\ \E n \in TraceNodes :
        RequestVote(n)

IsHandleVoteRequest ==
    /\ IsEvent("HandleVoteRequest")
    /\ \E n \in TraceNodes :
        /\ \E msg \in Tracemessages :
            HandleVoteRequest(n, msg)

IsHandleVoteResponse ==
    /\ IsEvent("HandleVoteResponse")
    /\ \E n \in TraceNodes :
        /\ \E msg \in Tracemessages :
            HandleVoteResponse(n, msg)

IsAppendEntries ==
    /\ IsEvent("AppendEntries")
    /\ \E n \in TraceNodes :
        AppendEntries(n)

IsHandleAppendRequest ==
    /\ IsEvent("HandleAppendRequest")
    /\ \E n \in TraceNodes :
        /\ \E msg \in Tracemessages :
            HandleAppendRequest(n, msg)

IsHandleAppendResponse ==
    /\ IsEvent("HandleAppendResponse")
    /\ \E n \in TraceNodes :
        /\ \E msg \in Tracemessages :
            HandleAppendResponse(n, msg)

IsAdvanceCommitIndex ==
    /\ IsEvent("AdvanceCommitIndex")
    /\ \E n \in TraceNodes :
        AdvanceCommitIndex(n)

IsElectionTimeout ==
    /\ IsEvent("ElectionTimeout")
    /\ \E n \in TraceNodes :
        ElectionTimeout(n)

IsHeartbeatTimeout ==
    /\ IsEvent("HeartbeatTimeout")
    /\ \E n \in TraceNodes :
        HeartbeatTimeout(n)

IsHandleHeartbeat ==
    /\ IsEvent("HandleHeartbeat")
    /\ \E n \in TraceNodes :
        /\ \E msg \in Tracemessages :
            HandleHeartbeat(n, msg)

IsHandleHeartbeatResponse ==
    /\ IsEvent("HandleHeartbeatResponse")
    /\ \E n \in TraceNodes :
        /\ \E msg \in Tracemessages :
            HandleHeartbeatResponse(n, msg)

(* State transition definition *)
TraceNextImpl ==
    \/ IsBecomeCandidate
    \/ IsBecomeLeader
    \/ IsRequestVote
    \/ IsHandleVoteRequest
    \/ IsHandleVoteResponse
    \/ IsAppendEntries
    \/ IsHandleAppendRequest
    \/ IsHandleAppendResponse
    \/ IsAdvanceCommitIndex
    \/ IsElectionTimeout
    \/ IsHeartbeatTimeout
    \/ IsHandleHeartbeat
    \/ IsHandleHeartbeatResponse


(* REPLACE / MODIFY COMMENT BELOW ONLY IF YOU WANT TO MAKE ACTION COMPOSITION *)
ComposedNext == FALSE

(* NOTHING TO CHANGE BELOW *)
BaseSpec == Init /\ [][Next \/ ComposedNext]_vars

=============================================================================

