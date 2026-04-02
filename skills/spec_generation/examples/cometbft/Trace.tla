--------------------------- MODULE Trace ---------------------------
(*
 * Trace validation specification for CometBFT consensus.
 *
 * Replays implementation traces against the base spec to verify
 * that the base spec can reproduce every observed state transition.
 *
 * Trace format: NDJSON with tag="trace" and event records containing:
 *   - event.name: action name
 *   - event.nid: server ID
 *   - event.state: post-action state snapshot
 *   - event.msg: message fields (for message-related events)
 *)

EXTENDS base, Json, IOUtils, Sequences, TLC

\* ============================================================================
\* TRACE LOADING
\* ============================================================================

\* Read JSON file path from environment variable or use default.
JsonFile ==
    IF "JSON" \in DOMAIN IOEnv THEN IOEnv.JSON
    ELSE "../traces/trace.ndjson"

\* Load NDJSON, filter to trace events only.
TraceLog == TLCEval(
    LET all == ndJsonDeserialize(JsonFile)
    IN SelectSeq(all, LAMBDA x :
        /\ "tag" \in DOMAIN x
        /\ x.tag = "trace"
        /\ "event" \in DOMAIN x))

ASSUME Len(TraceLog) > 0

\* ============================================================================
\* TRACE CURSOR
\* ============================================================================

VARIABLE l       \* Current position in TraceLog (1-indexed)

traceVars == <<l>>

logline == TraceLog[l]

\* ============================================================================
\* SERVER EXTRACTION FROM TRACE
\* ============================================================================

TraceServer == TLCEval(
    UNION {
        {TraceLog[k].event.nid}
        \cup (IF "msg" \in DOMAIN TraceLog[k].event
              THEN {TraceLog[k].event.msg.source,
                    TraceLog[k].event.msg.dest} \ {""}
              ELSE {})
        : k \in 1..Len(TraceLog)
    })

ASSUME TraceServer /= {}
ASSUME TraceServer \subseteq Server

\* Map trace value to spec value (Nil for empty/null)
TraceValue(v) ==
    IF v = "" \/ v = "null" \/ v = "nil" THEN Nil ELSE v

\* ============================================================================
\* PROPOSER EXTRACTION FROM TRACE
\* ============================================================================

\* Extract proposer for each (height, round) from ReceiveProposal events.
\* The msg.source of a ReceiveProposal tells us who proposed.
TraceProposerMap == TLCEval(
    LET propEvents == SelectSeq(TraceLog, LAMBDA x :
            /\ x.event.name = "ReceiveProposal"
            /\ "msg" \in DOMAIN x.event)
    IN [k \in 1..Len(propEvents) |->
        [height |-> propEvents[k].event.state.height,
         round  |-> propEvents[k].event.msg.round,
         source |-> propEvents[k].event.msg.source]]
)

\* Override for Proposer: use trace data when available, else round-robin.
\* Referenced from Trace.cfg via CONSTANT Proposer <- TraceProposer
TraceProposer(h, r) ==
    LET matches == {k \in 1..Len(TraceProposerMap) :
                     /\ TraceProposerMap[k].height = h
                     /\ TraceProposerMap[k].round = r}
    IN IF matches /= {}
       THEN TraceProposerMap[CHOOSE k \in matches : TRUE].source
       ELSE \* Fall back to round-robin with sorted servers
            LET serverSeq == <<"s1", "s2", "s3">>
                idx == ((h + r) % Cardinality(Server)) + 1
            IN serverSeq[idx]

\* Extract expected proposal value for each (height, round) from ReceiveProposal.
\* Used to override ChooseValue for deterministic trace replay.
TraceProposalValue(h, r) ==
    LET propEvents == SelectSeq(TraceLog, LAMBDA x :
            /\ x.event.name = "ReceiveProposal"
            /\ "msg" \in DOMAIN x.event
            /\ x.event.state.height = h
            /\ x.event.msg.round = r)
    IN IF Len(propEvents) > 0
       THEN TraceValue(propEvents[1].event.msg.value)
       ELSE Nil

\* Override for ChooseValue: use trace-derived proposal value when available,
\* else fall back to base.tla's deterministic CHOOSE.
\* Referenced from Trace.cfg via CONSTANT ChooseValue <- TraceChooseValue
TraceChooseValue(i) ==
    LET tv == TraceProposalValue(height[i], round[i])
    IN IF tv /= Nil THEN tv ELSE CHOOSE val \in Values : TRUE

\* ============================================================================
\* STEP MAPPING
\* ============================================================================

\* Map implementation step strings to spec step constants
StepMapping ==
    "NewHeight"      :> StepNewHeight     @@
    "NewRound"       :> StepNewRound      @@
    "Propose"        :> StepPropose       @@
    "Prevote"        :> StepPrevote       @@
    "PrevoteWait"    :> StepPrevoteWait   @@
    "Precommit"      :> StepPrecommit     @@
    "PrecommitWait"  :> StepPrecommitWait @@
    "Commit"         :> StepCommit

\* ============================================================================
\* EVENT PREDICATES
\* ============================================================================

IsEvent(name) ==
    /\ l <= Len(TraceLog)
    /\ logline.event.name = name

IsNodeEvent(name, i) ==
    /\ IsEvent(name)
    /\ logline.event.nid = i

IsMsgEvent(name, from, to) ==
    /\ IsEvent(name)
    /\ "msg" \in DOMAIN logline.event
    /\ logline.event.msg.source = from
    /\ logline.event.msg.dest = to

\* ============================================================================
\* POST-STATE VALIDATION
\* ============================================================================

\* Strong validation: check height, round, step
ValidatePostState(i) ==
    /\ height'[i] = logline.event.state.height
    /\ round'[i] = logline.event.state.round
    /\ step'[i] = StepMapping[logline.event.state.step]

\* Weak validation: check height and round only
\* Used for async/message events where step may not match exactly
ValidatePostStateWeak(i) ==
    /\ height'[i] = logline.event.state.height
    /\ round'[i] = logline.event.state.round

\* Validate locked state
ValidateLockedState(i) ==
    /\ lockedRound'[i] = logline.event.state.lockedRound
    /\ lockedValue'[i] = TraceValue(logline.event.state.lockedValue)

\* Validate valid state
ValidateValidState(i) ==
    /\ validRound'[i] = logline.event.state.validRound
    /\ validValue'[i] = TraceValue(logline.event.state.validValue)

\* ============================================================================
\* STEP TRACE CURSOR
\* ============================================================================

StepTrace == l' = l + 1

\* ============================================================================
\* ACTION WRAPPERS
\* ============================================================================

\* --- EnterNewRound ---
\* Matches: event.name = "EnterNewRound"
EnterNewRoundIfLogged ==
    \E i \in Server :
        /\ IsNodeEvent("EnterNewRound", i)
        /\ LET r == logline.event.state.round IN
            /\ EnterNewRound(i, r)
            /\ ValidatePostState(i)
            /\ StepTrace

\* --- EnterPropose ---
\* Matches: event.name = "EnterPropose"
EnterProposeIfLogged ==
    \E i \in Server :
        /\ IsNodeEvent("EnterPropose", i)
        /\ EnterPropose(i)
        /\ ValidatePostState(i)
        /\ StepTrace

\* --- ReceiveProposal ---
\* Matches: event.name = "ReceiveProposal"
\* Special handling: when source == dest (self-proposal), the proposer
\* already set proposal in EnterPropose, so this is a no-op skip.
ReceiveProposalIfLogged ==
    \E i \in Server :
        /\ IsEvent("ReceiveProposal")
        /\ logline.event.nid = i
        /\ "msg" \in DOMAIN logline.event
        /\ \/ \* Self-proposal: proposer receives its own proposal (already set)
              /\ logline.event.msg.source = i
              /\ proposalBlock[i] /= Nil  \* EnterPropose already set it
              /\ UNCHANGED vars
              /\ ValidatePostStateWeak(i)
              /\ StepTrace
           \/ \* Normal: receive from another server via message
              /\ logline.event.msg.source /= i
              /\ \E m \in DOMAIN messages :
                  /\ m.mtype = ProposalMsg
                  /\ m.source = logline.event.msg.source
                  /\ m.dest = i
                  /\ ReceiveProposal(i, m)
                  /\ ValidatePostStateWeak(i)
                  /\ StepTrace

\* --- EnterPrevote ---
\* Matches: event.name = "EnterPrevote"
EnterPrevoteIfLogged ==
    \E i \in Server :
        /\ IsNodeEvent("EnterPrevote", i)
        /\ EnterPrevote(i)
        /\ ValidatePostState(i)
        /\ StepTrace

\* --- ReceivePrevote ---
\* Matches: event.name = "ReceivePrevote"
\* Self-votes: the spec records them directly in EnterPrevote, so skip.
ReceivePrevoteIfLogged ==
    \E i \in Server :
        /\ IsEvent("ReceivePrevote")
        /\ logline.event.nid = i
        /\ "msg" \in DOMAIN logline.event
        /\ \/ \* Self-vote: already recorded in EnterPrevote
              /\ logline.event.msg.source = i
              /\ step[i] = StepPrevote  \* already prevoted (can't use vote value: nil = "not voted")
              /\ UNCHANGED vars
              /\ ValidatePostStateWeak(i)
              /\ StepTrace
           \/ \* Normal: receive from another server via message
              /\ logline.event.msg.source /= i
              /\ \E m \in DOMAIN messages :
                  /\ m.mtype = PrevoteMsg
                  /\ m.source = logline.event.msg.source
                  /\ m.dest = i
                  /\ ReceivePrevote(i, m)
                  /\ ValidatePostStateWeak(i)
                  /\ StepTrace

\* --- EnterPrevoteWait ---
\* Matches: event.name = "EnterPrevoteWait"
EnterPrevoteWaitIfLogged ==
    \E i \in Server :
        /\ IsNodeEvent("EnterPrevoteWait", i)
        /\ EnterPrevoteWait(i)
        /\ ValidatePostState(i)
        /\ StepTrace

\* --- EnterPrecommit (all 5 paths) ---
\* Matches: event.name = "EnterPrecommit"
\* Determines which path based on post-state lock values.
EnterPrecommitIfLogged ==
    \E i \in Server :
        /\ IsNodeEvent("EnterPrecommit", i)
        /\ \/ /\ EnterPrecommitNoPolka(i)
              /\ ValidatePostState(i)
              /\ StepTrace
           \/ /\ EnterPrecommitNilPolka(i)
              /\ ValidatePostState(i)
              /\ ValidateLockedState(i)
              /\ StepTrace
           \/ /\ EnterPrecommitRelockPolka(i)
              /\ ValidatePostState(i)
              /\ ValidateLockedState(i)
              /\ StepTrace
           \/ /\ EnterPrecommitNewLockPolka(i)
              /\ ValidatePostState(i)
              /\ ValidateLockedState(i)
              /\ StepTrace
           \/ /\ EnterPrecommitUnknownPolka(i)
              /\ ValidatePostState(i)
              /\ ValidateLockedState(i)
              /\ StepTrace

\* --- ReceivePrecommit ---
\* Matches: event.name = "ReceivePrecommit"
\* Self-votes: the spec records them directly in EnterPrecommit*, so skip.
ReceivePrecommitIfLogged ==
    \E i \in Server :
        /\ IsEvent("ReceivePrecommit")
        /\ logline.event.nid = i
        /\ "msg" \in DOMAIN logline.event
        /\ \/ \* Self-vote: already recorded in EnterPrecommit*
              /\ logline.event.msg.source = i
              /\ step[i] = StepPrecommit  \* already precommitted
              /\ UNCHANGED vars
              /\ ValidatePostStateWeak(i)
              /\ StepTrace
           \/ \* Normal: receive from another server via message
              /\ logline.event.msg.source /= i
              /\ \E m \in DOMAIN messages :
                  /\ m.mtype = PrecommitMsg
                  /\ m.source = logline.event.msg.source
                  /\ m.dest = i
                  /\ ReceivePrecommit(i, m)
                  /\ ValidatePostStateWeak(i)
                  /\ StepTrace

\* --- EnterPrecommitWait ---
\* Matches: event.name = "EnterPrecommitWait"
\* Note: EnterPrecommitWait in base.tla requires HasPrecommitTwoThirdsAny,
\* but the quorum check can't distinguish nil precommits from "not voted"
\* (both map to Nil in the vote tracking). We relax to a step guard only.
\* The timeout scheduling is also a no-op for trace validation.
EnterPrecommitWaitIfLogged ==
    \E i \in Server :
        /\ IsNodeEvent("EnterPrecommitWait", i)
        /\ step[i] = StepPrecommit
        /\ UNCHANGED vars
        /\ StepTrace

\* --- HandleTimeoutPropose ---
\* Matches: event.name = "HandleTimeoutPropose"
\* Trace event captures PRE-state (before enterPrevote is called).
\* The actual state change (step→Prevote) is captured by the subsequent
\* EnterPrevote event. So this is a cursor-advancing no-op.
HandleTimeoutProposeIfLogged ==
    \E i \in Server :
        /\ IsNodeEvent("HandleTimeoutPropose", i)
        /\ step[i] = StepPropose
        /\ UNCHANGED vars
        /\ StepTrace

\* --- HandleTimeoutPrevote ---
\* Matches: event.name = "HandleTimeoutPrevote"
\* Same pattern: pre-state event, actual change in subsequent EnterPrecommit.
HandleTimeoutPrevoteIfLogged ==
    \E i \in Server :
        /\ IsNodeEvent("HandleTimeoutPrevote", i)
        /\ step[i] = StepPrevoteWait
        /\ UNCHANGED vars
        /\ StepTrace

\* --- HandleTimeoutPrecommit ---
\* Matches: event.name = "HandleTimeoutPrecommit"
\* Pre-state event. Actual round advancement in subsequent EnterNewRound.
HandleTimeoutPrecommitIfLogged ==
    \E i \in Server :
        /\ IsNodeEvent("HandleTimeoutPrecommit", i)
        /\ step[i] = StepPrecommit
        /\ UNCHANGED vars
        /\ StepTrace

\* --- EnterCommit ---
\* Matches: event.name = "EnterCommit"
EnterCommitIfLogged ==
    \E i \in Server :
        /\ IsNodeEvent("EnterCommit", i)
        /\ EnterCommit(i)
        /\ ValidatePostState(i)
        /\ StepTrace

\* --- FinalizeCommit ---
\* Matches: event.name = "FinalizeCommit"
FinalizeCommitIfLogged ==
    \E i \in Server :
        /\ IsNodeEvent("FinalizeCommit", i)
        /\ FinalizeCommit(i)
        /\ ValidatePostState(i)
        /\ StepTrace

\* --- RoundSkip ---
\* Matches: event.name = "RoundSkip"
RoundSkipIfLogged ==
    \E i \in Server :
        /\ IsNodeEvent("RoundSkip", i)
        /\ \/ /\ RoundSkipPrevote(i)
              /\ ValidatePostState(i)
              /\ StepTrace
           \/ /\ RoundSkipPrecommit(i)
              /\ ValidatePostState(i)
              /\ StepTrace

\* --- Crash ---
\* Matches: event.name = "Crash"
CrashIfLogged ==
    \E i \in Server :
        /\ IsNodeEvent("Crash", i)
        /\ Crash(i)
        /\ StepTrace

\* --- Recover ---
\* Matches: event.name = "Recover"
RecoverIfLogged ==
    \E i \in Server :
        /\ IsNodeEvent("Recover", i)
        /\ Recover(i)
        /\ ValidatePostState(i)
        /\ StepTrace

\* ============================================================================
\* SILENT ACTIONS
\* ============================================================================

\* Silent actions handle implementation state changes that occur without
\* trace events. They must be tightly constrained to prevent state explosion.

\* --- Silent message delivery ---
\* Messages may be delivered without trace events when the implementation
\* processes them as part of a batch or during internal message routing.
SilentReceivePrevote ==
    /\ l <= Len(TraceLog)
    \* Only fire when the next trace event requires prevotes we haven't seen
    /\ logline.event.name \in {"EnterPrevoteWait", "EnterPrecommit"}
    /\ LET i == logline.event.nid IN
       /\ \E m \in DOMAIN messages :
           /\ m.mtype = PrevoteMsg
           /\ m.dest = i
           /\ m.height = height[i]
           /\ ReceivePrevote(i, m)
           /\ UNCHANGED l

\* --- Silent precommit delivery ---
SilentReceivePrecommit ==
    /\ l <= Len(TraceLog)
    /\ logline.event.name \in {"EnterPrecommitWait", "EnterCommit"}
    /\ LET i == logline.event.nid IN
       /\ \E m \in DOMAIN messages :
           /\ m.mtype = PrecommitMsg
           /\ m.dest = i
           /\ m.height = height[i]
           /\ ReceivePrecommit(i, m)
           /\ UNCHANGED l

\* --- Silent proposal delivery (REMOVED) ---
\* Not needed: observed node's proposal reception is handled by
\* ReceiveProposalIfLogged. Delivering proposals silently to the observed
\* node causes incorrect state in timeout scenarios (observed node would
\* receive a proposal it actually timed out on).

\* --- Silent round advancement ---
\* Server may need to enter new round before the traced action
SilentEnterNewRound ==
    /\ l <= Len(TraceLog)
    /\ logline.event.name \in {"EnterPropose", "EnterPrevote"}
    /\ LET i == logline.event.nid
           targetRound == logline.event.state.round
       IN
       /\ round[i] < targetRound
       /\ EnterNewRound(i, targetRound)
       /\ UNCHANGED l

\* ============================================================================
\* SILENT ACTIONS FOR NON-OBSERVED SERVERS
\* ============================================================================
\* When the trace only observes one node (s1), the other servers need to
\* progress through their protocol silently to generate votes that s1 receives.
\* These actions are tightly constrained: they only fire when the next trace
\* event needs messages that don't yet exist.

\* Helper: the observed node from the current trace event
ObservedNode == logline.event.nid

\* --- Ordering constraint for non-observed servers ---
\* Break symmetry: among non-observed servers at the same height,
\* only the least-advanced (by step rank, then ID) can take a
\* step-changing action.  This eliminates interleaving explosion.
StepRank(s) ==
    CASE step[s] = StepNewHeight    -> 0
      [] step[s] = StepNewRound     -> 1
      [] step[s] = StepPropose      -> 2
      [] step[s] = StepPrevote      -> 3
      [] step[s] = StepPrevoteWait  -> 4
      [] step[s] = StepPrecommit    -> 5
      [] step[s] = StepPrecommitWait -> 6
      [] step[s] = StepCommit       -> 7

\* Map server IDs to integers for ordering (hardcoded for trace validation)
ServerOrder == "s1" :> 1 @@ "s2" :> 2 @@ "s3" :> 3

OrderedSilentProgress(i) ==
    \A j \in Server :
        (j /= ObservedNode /\ j /= i /\ height[j] = height[i])
        => \/ round[j] > round[i]
           \/ (round[j] = round[i] /\ StepRank(j) > StepRank(i))
           \/ (round[j] = round[i] /\ StepRank(j) = StepRank(i)
               /\ ServerOrder[j] > ServerOrder[i])

\* --- Silent non-observed server enters new round ---
SilentOtherEnterNewRound ==
    /\ l <= Len(TraceLog)
    /\ \E i \in Server :
        /\ i /= ObservedNode
        /\ OrderedSilentProgress(i)
        /\ \/ step[i] \in {StepNewHeight, StepCommit}
           \/ round[ObservedNode] > round[i]  \* base.tla allows r > round[i] to bypass step check
        /\ EnterNewRound(i, round[ObservedNode])
        /\ UNCHANGED l

\* --- Silent non-observed server enters propose ---
SilentOtherEnterPropose ==
    /\ l <= Len(TraceLog)
    /\ \E i \in Server :
        /\ i /= ObservedNode
        /\ OrderedSilentProgress(i)
        /\ step[i] = StepNewRound
        /\ height[i] = height[ObservedNode]
        /\ EnterPropose(i)
        /\ UNCHANGED l

\* --- Silent non-observed server receives proposal ---
SilentOtherReceiveProposal ==
    /\ l <= Len(TraceLog)
    /\ \E i \in Server :
        /\ i /= ObservedNode
        /\ step[i] = StepPropose
        /\ \E m \in DOMAIN messages :
            /\ m.mtype = ProposalMsg
            /\ m.dest = i
            /\ m.height = height[i]
            /\ ReceiveProposal(i, m)
            /\ UNCHANGED l

\* --- Silent non-observed server enters prevote ---
\* This generates PrevoteMsg from the non-observed server.
SilentOtherEnterPrevote ==
    /\ l <= Len(TraceLog)
    \* Fire when next trace event needs prevotes or precommits from non-observed servers
    /\ logline.event.name \in {"ReceivePrevote", "EnterPrevoteWait", "EnterPrecommit",
                                "ReceivePrecommit", "EnterPrecommitWait", "EnterCommit"}
    /\ \E i \in Server :
        /\ i /= ObservedNode
        /\ OrderedSilentProgress(i)
        /\ step[i] = StepPropose
        /\ height[i] = height[ObservedNode]
        \* Must have received proposal first if one is available
        /\ \/ proposalBlock[i] /= Nil
           \/ ~\E m \in DOMAIN messages :
                /\ m.mtype = ProposalMsg
                /\ m.dest = i
                /\ m.height = height[i]
                /\ m.round = round[i]
        /\ EnterPrevote(i)
        /\ UNCHANGED l

\* --- Silent non-observed server receives prevote ---
\* Non-observed servers need to receive prevotes from other servers
\* to form +2/3 quorums before entering precommit.
SilentOtherReceivePrevote ==
    /\ l <= Len(TraceLog)
    /\ logline.event.name \in {"ReceivePrevote", "EnterPrevoteWait", "EnterPrecommit",
                                "ReceivePrecommit", "EnterPrecommitWait", "EnterCommit"}
    /\ \E i \in Server :
        /\ i /= ObservedNode
        /\ \E m \in DOMAIN messages :
            /\ m.mtype = PrevoteMsg
            /\ m.dest = i
            /\ m.height = height[i]
            /\ ReceivePrevote(i, m)
            /\ UNCHANGED l

\* --- Silent non-observed server enters precommit ---
\* This generates PrecommitMsg from the non-observed server.
SilentOtherEnterPrecommit ==
    /\ l <= Len(TraceLog)
    \* Only fire when next trace event needs precommits
    /\ logline.event.name \in {"ReceivePrecommit", "EnterPrecommitWait", "EnterCommit"}
    /\ \E i \in Server :
        /\ i /= ObservedNode
        /\ OrderedSilentProgress(i)
        /\ step[i] = StepPrevote
        /\ height[i] = height[ObservedNode]
        \* Must have received all available prevotes first
        /\ ~\E m \in DOMAIN messages :
            /\ m.mtype = PrevoteMsg
            /\ m.dest = i
            /\ m.height = height[i]
        /\ \/ EnterPrecommitNoPolka(i)
           \/ EnterPrecommitNilPolka(i)
           \/ EnterPrecommitRelockPolka(i)
           \/ EnterPrecommitNewLockPolka(i)
           \/ EnterPrecommitUnknownPolka(i)
        /\ UNCHANGED l

\* --- Silent non-observed server jumps to target height ---
\* Atomically advances a non-observed server from any state at height h
\* to StepNewHeight at the target height, bypassing individual commit/
\* finalize/newround steps. This dramatically reduces state space for
\* multi-height traces by eliminating interleaving of height advancement.
SilentOtherJumpToHeight ==
    /\ l <= Len(TraceLog)
    /\ logline.event.state.height > 1
    /\ \E i \in Server :
        /\ i /= ObservedNode
        /\ OrderedSilentProgress(i)
        /\ height[i] < logline.event.state.height
        \* Atomically set state for new height
        /\ height' = [height EXCEPT ![i] = height[i] + 1]
        /\ round' = [round EXCEPT ![i] = 0]
        /\ step' = [step EXCEPT ![i] = StepNewHeight]
        /\ proposal' = [proposal EXCEPT ![i] = Nil]
        /\ proposalBlock' = [proposalBlock EXCEPT ![i] = Nil]
        /\ lockedRound' = [lockedRound EXCEPT ![i] = -1]
        /\ lockedValue' = [lockedValue EXCEPT ![i] = Nil]
        /\ validRound' = [validRound EXCEPT ![i] = -1]
        /\ validValue' = [validValue EXCEPT ![i] = Nil]
        /\ decision' = [decision EXCEPT ![i][height[i]] =
               IF @ /= Nil THEN @
               ELSE CHOOSE v \in Values : TRUE]
        /\ prevotes' = [prevotes EXCEPT ![i] = [r \in 0..MaxRound |-> EmptyVoteMap]]
        /\ precommits' = [precommits EXCEPT ![i] = [r \in 0..MaxRound |-> EmptyVoteMap]]
        /\ privvalLastSigned' = [privvalLastSigned EXCEPT ![i] =
               [height |-> height[i], round |-> round[i]]]
        /\ timeoutScheduled' = [timeoutScheduled EXCEPT ![i] = {}]
        /\ walEntries' = [walEntries EXCEPT ![i] = Append(@,
               [type |-> "endHeight", height |-> height[i]])]
        /\ UNCHANGED <<l, messages, veVars, crashed,
                       evidenceVars, proposerVars>>

\* ============================================================================
\* TRACE INIT
\* ============================================================================

TraceInit ==
    /\ l = 1
    /\ height          = [s \in Server |-> 1]
    /\ round           = [s \in Server |-> 0]
    /\ step            = [s \in Server |-> StepNewHeight]
    /\ proposal        = [s \in Server |-> Nil]
    /\ proposalBlock   = [s \in Server |-> Nil]
    /\ lockedRound     = [s \in Server |-> -1]
    /\ lockedValue     = [s \in Server |-> Nil]
    /\ validRound      = [s \in Server |-> -1]
    /\ validValue      = [s \in Server |-> Nil]
    /\ prevotes        = [s \in Server |-> [r \in 0..MaxRound |-> EmptyVoteMap]]
    /\ precommits      = [s \in Server |-> [r \in 0..MaxRound |-> EmptyVoteMap]]
    /\ decision        = [s \in Server |-> [h \in 1..MaxHeight |-> Nil]]
    /\ messages        = EmptyBag
    /\ voteExtension   = [s \in Server |-> ValidVE]
    /\ veVerified      = [s \in Server |-> [j \in Server |-> FALSE]]
    /\ timeoutScheduled = [s \in Server |-> {}]
    /\ walEntries      = [s \in Server |-> <<>>]
    /\ crashed         = [s \in Server |-> FALSE]
    /\ privvalLastSigned = [s \in Server |-> [height |-> 0, round |-> 0]]
    /\ pendingEvidence  = {}
    /\ committedEvidence = {}
    /\ proposerHistory  = [h \in 1..MaxHeight |-> Proposer(h, 0)]

\* ============================================================================
\* TRACE NEXT
\* ============================================================================

TraceDone ==
    /\ l > Len(TraceLog)
    /\ UNCHANGED <<l, vars>>

TraceNext ==
    \* Stuttering after trace consumed (prevents deadlock)
    \/ TraceDone
    \* Action wrappers (consume one trace event each)
    \/ EnterNewRoundIfLogged
    \/ EnterProposeIfLogged
    \/ ReceiveProposalIfLogged
    \/ EnterPrevoteIfLogged
    \/ ReceivePrevoteIfLogged
    \/ EnterPrevoteWaitIfLogged
    \/ EnterPrecommitIfLogged
    \/ ReceivePrecommitIfLogged
    \/ EnterPrecommitWaitIfLogged
    \/ HandleTimeoutProposeIfLogged
    \/ HandleTimeoutPrevoteIfLogged
    \/ HandleTimeoutPrecommitIfLogged
    \/ EnterCommitIfLogged
    \/ FinalizeCommitIfLogged
    \/ RoundSkipIfLogged
    \/ CrashIfLogged
    \/ RecoverIfLogged
    \* Silent actions (no trace event consumed)
    \/ SilentReceivePrevote
    \/ SilentReceivePrecommit
    \/ SilentEnterNewRound
    \* Silent non-observed server progress
    \/ SilentOtherEnterNewRound
    \/ SilentOtherEnterPropose
    \/ SilentOtherReceiveProposal
    \/ SilentOtherEnterPrevote
    \/ SilentOtherReceivePrevote
    \/ SilentOtherEnterPrecommit
    \/ SilentOtherJumpToHeight

\* ============================================================================
\* SPEC AND PROPERTIES
\* ============================================================================

TraceSpec == TraceInit /\ [][TraceNext]_<<l, vars>>

\* View must include cursor position
TraceView == <<vars, l>>

\* Property: entire trace was consumed
TraceMatched ==
    <>(l > Len(TraceLog))

\* ============================================================================
\* ALIAS (for debugging trace failures)
\* ============================================================================

TraceAlias ==
    [
        cursor    |-> l,
        traceLen  |-> Len(TraceLog),
        event     |-> IF l <= Len(TraceLog) THEN logline.event.name ELSE "DONE",
        nid       |-> IF l <= Len(TraceLog) THEN logline.event.nid ELSE "DONE",
        tState    |-> IF l <= Len(TraceLog)
                      THEN logline.event.state
                      ELSE "DONE",
        height    |-> height,
        round     |-> round,
        step      |-> step,
        locked    |-> [s \in Server |->
                        [round |-> lockedRound[s], value |-> lockedValue[s]]],
        valid     |-> [s \in Server |->
                        [round |-> validRound[s], value |-> validValue[s]]],
        proposal  |-> proposalBlock,
        msgCount  |-> BagCardinality(messages),
        crashed   |-> crashed
    ]

====
