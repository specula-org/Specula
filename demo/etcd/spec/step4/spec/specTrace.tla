--------------------------- MODULE specTrace ---------------------------

EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags, Json, IOUtils, Raft, TraceSpec, TVOperators

allVars == <<vars, pc, info, stack>>

TraceNil == "null"

(* Extract system configuration from first trace line *)
TraceServer == ToSet(Trace[1].Server)
TraceMaxTerm == ToSet(Trace[1].MaxTerm)
TraceMaxLogLen == ToSet(Trace[1].MaxLogLen)
TraceNone == ToSet(Trace[1].None)

(* Default variable initialization *)
DefaultImpl(varName) ==
    CASE varName = "state" -> [s \in TraceServer |-> StateFollower]
     [] varName = "currentTerm" -> [s \in TraceServer |-> 0]
     [] varName = "votedFor" -> [s \in TraceServer |-> TraceNone]
     [] varName = "log" -> [s \in TraceServer |-> <<>>]
     [] varName = "commitIndex" -> [s \in TraceServer |-> 0]
     [] varName = "leaderId" -> [s \in TraceServer |-> TraceNone]
     [] varName = "matchIndex" -> [s \in TraceServer |-> [t \in TraceServer |-> 0]]
     [] varName = "nextIndex" -> [s \in TraceServer |-> [t \in TraceServer |-> 1]]
     [] varName = "votesGranted" -> [s \in TraceServer |-> [t \in TraceServer |-> FALSE]]
     [] varName = "pendingConfIndex" -> [s \in TraceServer |-> 0]
     [] varName = "uncommittedSize" -> [s \in TraceServer |-> 0]
     [] varName = "leadTransferee" -> [s \in TraceServer |-> TraceNone]
     [] varName = "isLearner" -> [s \in TraceServer |-> FALSE]
     [] varName = "electionElapsed" -> [s \in TraceServer |-> 0]
     [] varName = "heartbeatElapsed" -> [s \in TraceServer |-> 0]
     [] varName = "randomizedElectionTimeout" -> [s \in TraceServer |-> 10]
     [] varName = "messages" -> {}

(* State variable update logic *)
UpdateVariablesImpl(t) ==
    /\ IF "state" \in DOMAIN t
       THEN state' = UpdateVariable(state, "state", t)
       ELSE TRUE
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
    /\ IF "leaderId" \in DOMAIN t
       THEN leaderId' = UpdateVariable(leaderId, "leaderId", t)
       ELSE TRUE
    /\ IF "matchIndex" \in DOMAIN t
       THEN matchIndex' = UpdateVariable(matchIndex, "matchIndex", t)
       ELSE TRUE
    /\ IF "nextIndex" \in DOMAIN t
       THEN nextIndex' = UpdateVariable(nextIndex, "nextIndex", t)
       ELSE TRUE
    /\ IF "votesGranted" \in DOMAIN t
       THEN votesGranted' = UpdateVariable(votesGranted, "votesGranted", t)
       ELSE TRUE
    /\ IF "pendingConfIndex" \in DOMAIN t
       THEN pendingConfIndex' = UpdateVariable(pendingConfIndex, "pendingConfIndex", t)
       ELSE TRUE
    /\ IF "uncommittedSize" \in DOMAIN t
       THEN uncommittedSize' = UpdateVariable(uncommittedSize, "uncommittedSize", t)
       ELSE TRUE
    /\ IF "leadTransferee" \in DOMAIN t
       THEN leadTransferee' = UpdateVariable(leadTransferee, "leadTransferee", t)
       ELSE TRUE
    /\ IF "isLearner" \in DOMAIN t
       THEN isLearner' = UpdateVariable(isLearner, "isLearner", t)
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

(* Action event matching *)

IsStepElection ==
    /\ IsEvent("Step")
    /\ \E s \in TraceServer :
        /\ electionElapsed[s] >= randomizedElectionTimeout[s]
        /\ HandleStep(s, [type |-> MsgHup, from |-> s, to |-> s, term |-> currentTerm[s]])

IsStepMessage ==
    /\ IsEvent("Step")
    /\ \E m \in messages :
        /\ \E s \in TraceServer :
            /\ m.to = s
            /\ HandleStep(s, m)

(* State transition definition *)
TraceNextImpl ==
    \/ IsStepElection
    \/ IsStepMessage


(* REPLACE / MODIFY COMMENT BELOW ONLY IF YOU WANT TO MAKE ACTION COMPOSITION *)
ComposedNext == FALSE

(* NOTHING TO CHANGE BELOW *)
BaseSpec == Init /\ [][Next \/ ComposedNext]_vars

=============================================================================

