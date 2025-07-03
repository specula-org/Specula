--------------------------- MODULE specTrace ---------------------------

EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags, Json, IOUtils, Raft, TraceSpec, TVOperators


TraceNil == "null"

(* Extract system configuration from first trace line *)
TraceServer == ToSet(Trace[1].Server)
TraceValue == ToSet(Trace[1].Value)
TraceNoLimit == ToSet(Trace[1].NoLimit)

(* Default variable initialization *)
DefaultImpl(varName) ==
    CASE varName = "currentTerm" -> [s \in TraceServer |-> 0]
     [] varName = "votedFor" -> [s \in TraceServer |-> Nil]
     [] varName = "log" -> [s \in TraceServer |-> <<>>]
     [] varName = "commitIndex" -> [s \in TraceServer |-> 0]
     [] varName = "state" -> [s \in TraceServer |-> "Follower"]
     [] varName = "leaderId" -> [s \in TraceServer |-> Nil]
     [] varName = "nextIndex" -> [s \in TraceServer |-> [t \in TraceServer |-> 1]]
     [] varName = "matchIndex" -> [s \in TraceServer |-> [t \in TraceServer |-> 0]]
     [] varName = "votesGranted" -> [s \in TraceServer |-> {}]
     [] varName = "votesRejected" -> [s \in TraceServer |-> {}]
     [] varName = "electionElapsed" -> [s \in TraceServer |-> 0]
     [] varName = "heartbeatElapsed" -> [s \in TraceServer |-> 0]
     [] varName = "randomizedElectionTimeout" -> [s \in TraceServer |-> 3]
     [] varName = "messages" -> {}
     [] varName = "readStates" -> [s \in TraceServer |-> <<>>]
     [] varName = "pendingReadIndexMessages" -> [s \in TraceServer |-> <<>>]
     [] varName = "leadTransferee" -> [s \in TraceServer |-> Nil]
     [] varName = "pendingConfIndex" -> [s \in TraceServer |-> 0]
     [] varName = "uncommittedSize" -> [s \in TraceServer |-> 0]
     [] varName = "isLearner" -> [s \in TraceServer |-> FALSE]
     [] varName = "config" -> [s \in TraceServer |-> [voters: TraceServer, learners: {}]]
     [] varName = "readOnlyOption" -> [s \in TraceServer |-> "Safe"]

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
    /\ IF "votesGranted" \in DOMAIN t
       THEN votesGranted' = UpdateVariable(votesGranted, "votesGranted", t)
       ELSE TRUE
    /\ IF "votesRejected" \in DOMAIN t
       THEN votesRejected' = UpdateVariable(votesRejected, "votesRejected", t)
       ELSE TRUE
    /\ IF "electionElapsed" \in DOMAIN t
       THEN electionElapsed' = UpdateVariable(electionElapsed, "electionElapsed", t)
       ELSE TRUE
    /\ IF "heartbeatElapsed" \in DOMAIN t
       THEN heartbeatElapsed' = UpdateVariable(heartbeatElapsed, "heartbeatElapsed", t)
       ELSE TRUE
    /\ IF "randomizedElectionTimeout" \in DOMAIN t
       THEN randomizedElectionTimeout' = UpdateVariable(randomizedElectionTimeout, "randomizedElectionTimeout", t)
       ELSE TRUE
    /\ IF "messages" \in DOMAIN t
       THEN messages' = UpdateVariable(messages, "messages", t)
       ELSE TRUE
    /\ IF "readStates" \in DOMAIN t
       THEN readStates' = UpdateVariable(readStates, "readStates", t)
       ELSE TRUE
    /\ IF "pendingReadIndexMessages" \in DOMAIN t
       THEN pendingReadIndexMessages' = UpdateVariable(pendingReadIndexMessages, "pendingReadIndexMessages", t)
       ELSE TRUE
    /\ IF "leadTransferee" \in DOMAIN t
       THEN leadTransferee' = UpdateVariable(leadTransferee, "leadTransferee", t)
       ELSE TRUE
    /\ IF "pendingConfIndex" \in DOMAIN t
       THEN pendingConfIndex' = UpdateVariable(pendingConfIndex, "pendingConfIndex", t)
       ELSE TRUE
    /\ IF "uncommittedSize" \in DOMAIN t
       THEN uncommittedSize' = UpdateVariable(uncommittedSize, "uncommittedSize", t)
       ELSE TRUE
    /\ IF "isLearner" \in DOMAIN t
       THEN isLearner' = UpdateVariable(isLearner, "isLearner", t)
       ELSE TRUE
    /\ IF "config" \in DOMAIN t
       THEN config' = UpdateVariable(config, "config", t)
       ELSE TRUE
    /\ IF "readOnlyOption" \in DOMAIN t
       THEN readOnlyOption' = UpdateVariable(readOnlyOption, "readOnlyOption", t)
       ELSE TRUE

(* Action event matching *)

IstickElection ==
    /\ IsEvent("tickElection")
    /\ \E s \in TraceServer :
        HandletickElection(s)

IstickHeartbeat ==
    /\ IsEvent("tickHeartbeat")
    /\ \E s \in TraceServer :
        HandletickHeartbeat(s)

IsStep ==
    /\ IsEvent("Step")
    /\ \E s \in TraceServer :
        /\ \E m \in messages :
            /\ HandleStep(s, m)

IsSendClientRequest ==
    /\ IsEvent("SendClientRequest")
    /\ \E s \in TraceServer :
        SendClientRequest(s)

IsInter == 
    /\ pc # Nil
    /\ UNCHANGED <<l>>
    /\ \/ HandletickElection_1
       \/ HandletickHeartbeat_1
       \/ HandletickHeartbeat_1_2
       \/ HandleStep_1

(* State transition definition *)
TraceNextImpl ==
    \/ IstickElection
    \/ IstickHeartbeat
    \/ IsStep
    \/ IsSendClientRequest
    \/ IsInter


(* REPLACE / MODIFY COMMENT BELOW ONLY IF YOU WANT TO MAKE ACTION COMPOSITION *)
ComposedNext == FALSE

(* NOTHING TO CHANGE BELOW *)
BaseSpec == Init /\ [][Next \/ ComposedNext]_vars

=============================================================================

