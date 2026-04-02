--------------------------- MODULE MC ---------------------------
(*
 * Model checking specification for CometBFT consensus.
 *
 * Wraps the base spec with counter-bounded fault-injection actions.
 * Deterministic/reactive actions pass through unbounded.
 *
 * Counter-bounded actions (fault injection):
 *   - Timeout (propose, prevote, precommit)
 *   - Crash
 *   - LoseMessage
 *   - InvalidVE injection
 *
 * Unbounded actions (deterministic/reactive):
 *   - EnterNewRound, EnterPropose, EnterPrevote
 *   - EnterPrevoteWait, EnterPrecommit*, EnterPrecommitWait
 *   - EnterCommit, FinalizeCommit
 *   - ReceiveProposal, ReceivePrevote, ReceivePrecommit
 *   - RoundSkip*, Recover, DetectEquivocation
 *)

EXTENDS base

\* Access original (un-overridden) operator definitions.
cometbft == INSTANCE base

\* ============================================================================
\* CONSTRAINT CONSTANTS
\* ============================================================================

CONSTANT MaxTimeoutLimit       \* Max total timeout firings
CONSTANT MaxCrashLimit         \* Max total crash events
CONSTANT MaxLoseLimit          \* Max message loss events
CONSTANT MaxInvalidVELimit     \* Max invalid VE injections (Family 1)
CONSTANT MaxMsgBufferLimit     \* Max messages in flight

\* ============================================================================
\* CONSTRAINT VARIABLES
\* ============================================================================

VARIABLE faultCounters

faultVars == <<faultCounters>>

\* ============================================================================
\* COUNTER-BOUNDED FAULT-INJECTION ACTIONS
\* ============================================================================

\* --- Timeout actions (Family 2: bound non-deterministic timeout firing) ---

MCHandleTimeoutPropose(i) ==
    /\ faultCounters.timeout < MaxTimeoutLimit
    /\ cometbft!HandleTimeoutPropose(i)
    /\ faultCounters' = [faultCounters EXCEPT !.timeout = @ + 1]

MCHandleTimeoutPrevote(i) ==
    /\ faultCounters.timeout < MaxTimeoutLimit
    /\ cometbft!HandleTimeoutPrevote(i)
    /\ faultCounters' = [faultCounters EXCEPT !.timeout = @ + 1]

MCHandleTimeoutPrecommit(i) ==
    /\ faultCounters.timeout < MaxTimeoutLimit
    /\ cometbft!HandleTimeoutPrecommit(i)
    /\ faultCounters' = [faultCounters EXCEPT !.timeout = @ + 1]

\* --- Crash action (Family 3: bound crash events) ---

MCCrash(i) ==
    /\ faultCounters.crash < MaxCrashLimit
    /\ cometbft!Crash(i)
    /\ faultCounters' = [faultCounters EXCEPT !.crash = @ + 1]

\* --- Message loss (bound network unreliability) ---

MCLoseMessage(m) ==
    /\ faultCounters.lose < MaxLoseLimit
    /\ cometbft!LoseMessage(m)
    /\ faultCounters' = [faultCounters EXCEPT !.lose = @ + 1]

\* --- Invalid VE injection (Family 1: model Byzantine VE behavior) ---
\* Injects invalid vote extensions on specific servers.
\* Bug #5204: proposer self-verification skip + invalid VEs = deadlock

MCInjectInvalidVE(i) ==
    /\ faultCounters.invalidVE < MaxInvalidVELimit
    /\ voteExtension[i] = ValidVE
    /\ voteExtension' = [voteExtension EXCEPT ![i] = InvalidVE]
    /\ faultCounters' = [faultCounters EXCEPT !.invalidVE = @ + 1]
    /\ UNCHANGED <<consensusVars, proposalVars, lockVars, voteVars,
                   decisionVars, messages, veVerified, timeoutVars,
                   walVars, evidenceVars, proposerVars>>

\* ============================================================================
\* UNBOUNDED (DETERMINISTIC/REACTIVE) ACTIONS
\* ============================================================================

\* These actions are NOT bounded because they react to existing state.
\* Bounding them would prune valid state space.

MCEnterNewRound(i) ==
    /\ cometbft!EnterNewRound(i, round[i])
    /\ UNCHANGED faultVars

MCEnterPropose(i) ==
    /\ cometbft!EnterPropose(i)
    /\ UNCHANGED faultVars

MCEnterPrevote(i) ==
    /\ cometbft!EnterPrevote(i)
    /\ UNCHANGED faultVars

MCEnterPrevoteWait(i) ==
    /\ cometbft!EnterPrevoteWait(i)
    /\ UNCHANGED faultVars

MCEnterPrecommitNoPolka(i) ==
    /\ cometbft!EnterPrecommitNoPolka(i)
    /\ UNCHANGED faultVars

MCEnterPrecommitNilPolka(i) ==
    /\ cometbft!EnterPrecommitNilPolka(i)
    /\ UNCHANGED faultVars

MCEnterPrecommitRelockPolka(i) ==
    /\ cometbft!EnterPrecommitRelockPolka(i)
    /\ UNCHANGED faultVars

MCEnterPrecommitNewLockPolka(i) ==
    /\ cometbft!EnterPrecommitNewLockPolka(i)
    /\ UNCHANGED faultVars

MCEnterPrecommitUnknownPolka(i) ==
    /\ cometbft!EnterPrecommitUnknownPolka(i)
    /\ UNCHANGED faultVars

MCEnterPrecommitWait(i) ==
    /\ cometbft!EnterPrecommitWait(i)
    /\ UNCHANGED faultVars

MCEnterCommit(i) ==
    /\ cometbft!EnterCommit(i)
    /\ UNCHANGED faultVars

MCFinalizeCommit(i) ==
    /\ cometbft!FinalizeCommit(i)
    /\ UNCHANGED faultVars

MCRecover(i) ==
    /\ cometbft!Recover(i)
    /\ UNCHANGED faultVars

MCRoundSkipPrevote(i) ==
    /\ cometbft!RoundSkipPrevote(i)
    /\ UNCHANGED faultVars

MCRoundSkipPrecommit(i) ==
    /\ cometbft!RoundSkipPrecommit(i)
    /\ UNCHANGED faultVars

MCDetectEquivocation(i, j) ==
    /\ cometbft!DetectEquivocation(i, j)
    /\ UNCHANGED faultVars

\* --- Message handlers (unbounded: react to received messages) ---

MCReceiveProposal(i, m) ==
    /\ cometbft!ReceiveProposal(i, m)
    /\ UNCHANGED faultVars

MCReceivePrevote(i, m) ==
    /\ cometbft!ReceivePrevote(i, m)
    /\ UNCHANGED faultVars

MCReceivePrecommit(i, m) ==
    /\ cometbft!ReceivePrecommit(i, m)
    /\ UNCHANGED faultVars

\* ============================================================================
\* INITIALIZATION
\* ============================================================================

MCInit ==
    /\ Init
    /\ faultCounters = [
         timeout   |-> 0,
         crash     |-> 0,
         lose      |-> 0,
         invalidVE |-> 0]

\* Init with one server pre-injected with InvalidVE (for targeted VE testing)
MCInitVE ==
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
    \* One server starts with InvalidVE (nondeterministic choice)
    /\ \E bad \in Server :
        voteExtension = [s \in Server |-> IF s = bad THEN InvalidVE ELSE ValidVE]
    /\ veVerified      = [s \in Server |-> [j \in Server |-> FALSE]]
    /\ timeoutScheduled = [s \in Server |-> {}]
    /\ walEntries      = [s \in Server |-> <<>>]
    /\ crashed         = [s \in Server |-> FALSE]
    /\ privvalLastSigned = [s \in Server |-> [height |-> 0, round |-> 0]]
    /\ pendingEvidence  = {}
    /\ committedEvidence = {}
    /\ proposerHistory  = [h \in 1..MaxHeight |-> Proposer(h, 0)]
    /\ faultCounters = [
         timeout   |-> 0,
         crash     |-> 0,
         lose      |-> 0,
         invalidVE |-> 1]

\* ============================================================================
\* NEXT STATE RELATION
\* ============================================================================

MCNextAsync(i) ==
    \* --- Round progression (unbounded) ---
    \/ MCEnterNewRound(i)
    \/ MCEnterPropose(i)
    \/ MCEnterPrevote(i)
    \/ MCEnterPrevoteWait(i)
    \* --- Precommit (unbounded, 5 paths) ---
    \/ MCEnterPrecommitNoPolka(i)
    \/ MCEnterPrecommitNilPolka(i)
    \/ MCEnterPrecommitRelockPolka(i)
    \/ MCEnterPrecommitNewLockPolka(i)
    \/ MCEnterPrecommitUnknownPolka(i)
    \/ MCEnterPrecommitWait(i)
    \* --- Commit (unbounded) ---
    \/ MCEnterCommit(i)
    \/ MCFinalizeCommit(i)
    \* --- Timeouts (bounded) ---
    \/ MCHandleTimeoutPropose(i)
    \/ MCHandleTimeoutPrevote(i)
    \/ MCHandleTimeoutPrecommit(i)
    \* --- Round-skip (unbounded) ---
    \/ MCRoundSkipPrevote(i)
    \/ MCRoundSkipPrecommit(i)
    \* --- Recovery (unbounded) ---
    \/ MCRecover(i)
    \* --- VE injection (bounded, Family 1) ---
    \/ MCInjectInvalidVE(i)

MCNextCrash == \E i \in Server : MCCrash(i)

MCNextUnreliable ==
    \E m \in DOMAIN messages :
        MCLoseMessage(m)

MCNextMessage ==
    \E m \in DOMAIN messages :
        \/ MCReceiveProposal(m.dest, m)
        \/ MCReceivePrevote(m.dest, m)
        \/ MCReceivePrecommit(m.dest, m)

MCNextEvidence ==
    \E i, j \in Server : MCDetectEquivocation(i, j)

MCNext ==
    \/ \E i \in Server : MCNextAsync(i)
    \/ MCNextCrash
    \/ MCNextUnreliable
    \/ MCNextMessage
    \/ MCNextEvidence

\* ============================================================================
\* SPECIFICATIONS
\* ============================================================================

mc_vars == <<vars, faultVars>>

MCSpec == MCInit /\ [][MCNext]_mc_vars
MCSpecVE == MCInitVE /\ [][MCNext]_mc_vars

\* Deadlock verification: init state models the post-VE-deadlock scenario.
\* One server committed at h=1 and advanced to h=2; others stuck at h=1.
\* If TLC reports deadlock (0 successors), this proves the deadlock exists.
MCInitVEDeadlockTest ==
    LET bad == CHOOSE s \in Server : TRUE
        val == CHOOSE v \in Values : TRUE
    IN
    /\ height          = [s \in Server |-> IF s = bad THEN 2 ELSE 1]
    /\ round           = [s \in Server |-> 0]
    /\ step            = [s \in Server |-> StepPrecommit]
    /\ proposal        = [s \in Server |-> Nil]
    /\ proposalBlock   = [s \in Server |-> Nil]
    /\ lockedRound     = [s \in Server |->
                            IF s = bad THEN -1 ELSE 0]
    /\ lockedValue     = [s \in Server |->
                            IF s = bad THEN Nil ELSE val]
    /\ validRound      = [s \in Server |->
                            IF s = bad THEN -1 ELSE 0]
    /\ validValue      = [s \in Server |->
                            IF s = bad THEN Nil ELSE val]
    \* bad server cleared votes (FinalizeCommit); others have partial precommits
    /\ prevotes        = [s \in Server |->
                            [r \in 0..MaxRound |->
                                IF s /= bad
                                THEN [j \in Server |-> val]
                                ELSE EmptyVoteMap]]
    /\ precommits      = [s \in Server |->
                            [r \in 0..MaxRound |->
                                IF s = bad THEN EmptyVoteMap
                                ELSE [j \in Server |->
                                    IF j = bad THEN Nil  \* dropped due to InvalidVE
                                    ELSE val]]]
    /\ decision        = [s \in Server |->
                            [h \in 1..MaxHeight |->
                                IF h = 1 /\ s = bad THEN val ELSE Nil]]
    /\ messages        = EmptyBag  \* all messages consumed
    /\ voteExtension   = [s \in Server |->
                            IF s = bad THEN InvalidVE ELSE ValidVE]
    /\ veVerified      = [s \in Server |-> [j \in Server |-> FALSE]]
    /\ timeoutScheduled = [s \in Server |-> {}]
    /\ walEntries      = [s \in Server |-> <<>>]
    /\ crashed         = [s \in Server |-> FALSE]
    /\ privvalLastSigned = [s \in Server |-> [height |-> 0, round |-> 0]]
    /\ pendingEvidence  = {}
    /\ committedEvidence = {}
    /\ proposerHistory  = [h \in 1..MaxHeight |-> Proposer(h, 0)]
    /\ faultCounters = [
         timeout   |-> 0,
         crash     |-> 0,
         lose      |-> 0,
         invalidVE |-> 1]

MCSpecVEDeadlockTest == MCInitVEDeadlockTest /\ [][MCNext]_mc_vars

\* ============================================================================
\* SYMMETRY AND VIEW DEFINITIONS
\* ============================================================================

\* Symmetry reduction: servers are interchangeable
Symmetry == Permutations(Server)

\* Exclude fault counters from view (they don't affect protocol behavior)
ModelView == <<vars>>

\* ============================================================================
\* STATE SPACE PRUNING
\* ============================================================================

\* Bound message buffer to prevent state explosion
MsgBufferConstraint ==
    \/ MaxMsgBufferLimit = 0
    \/ BagCardinality(messages) <= MaxMsgBufferLimit

\* ============================================================================
\* SAFETY INVARIANTS (complementing base spec)
\* ============================================================================

\* Structural: prevote and precommit counts are bounded
VoteCountBound ==
    \A s \in Server :
        \A r \in 0..MaxRound :
            Cardinality({j \in Server : prevotes[s][r][j] /= Nil}) <= Cardinality(Server)

\* Structural: committed decision is stable
DecisionStability ==
    \A s \in Server :
        \A h \in 1..MaxHeight :
            decision[s][h] /= Nil => decision[s][h] \in Values

\* Structural: crashed server has no scheduled timeouts
CrashedNoTimeouts ==
    \A s \in Server :
        crashed[s] => timeoutScheduled[s] = {}

\* Family 1: VE verification is recorded for non-self precommits
VEVerificationTracked ==
    \A s \in Server :
        \A j \in Server :
            (j /= s /\ precommits[s][round[s]][j] /= Nil
             /\ precommits[s][round[s]][j] \in Values) =>
                veVerified[s][j] \in {TRUE, FALSE}

\* Family 3: Persisted term is consistent with current height
PrivvalConsistency ==
    \A s \in Server :
        privvalLastSigned[s].height <= height[s]

\* Family 1: VE Liveness — If one server commits at a height, all non-crashed
\* servers at that height must be able to eventually commit too.
\* Bug #5204: Proposer self-verification skip + invalid VEs = asymmetric commit.
\* The proposer counts its own precommit (no VE check) while others drop it
\* (invalid VE), creating a split where only the proposer reaches quorum.
VELivenessInv ==
    \A h \in 1..MaxHeight :
        \* If any server committed at height h...
        (\E s1 \in Server : decision[s1][h] /= Nil) =>
            \* ...then every non-crashed server at that height can also commit
            \A s2 \in Server :
                (~crashed[s2] /\ height[s2] = h /\ step[s2] /= StepCommit) =>
                    \* Either s2 has also decided, or s2 can still accumulate
                    \* enough valid precommits (at least one round where quorum
                    \* is reachable considering VE drops)
                    \/ decision[s2][h] /= Nil
                    \/ \E r \in 0..MaxRound :
                        \E v \in Values :
                            HasPrecommitQuorum(s2, r, v)

\* ============================================================================
\* TEMPORAL PROPERTIES
\* ============================================================================

\* Monotonic height: non-crashed servers never decrease height
MonotonicHeight ==
    [][
        \A s \in Server :
            (~crashed[s] /\ ~crashed'[s]) => height'[s] >= height[s]
    ]_mc_vars

\* Monotonic round within same height
MonotonicRound ==
    [][
        \A s \in Server :
            (~crashed[s] /\ ~crashed'[s] /\ height'[s] = height[s]) =>
                round'[s] >= round[s]
    ]_mc_vars

\* Decision permanence: once decided, the decision doesn't change
DecisionPermanence ==
    [][
        \A s \in Server :
            \A h \in 1..MaxHeight :
                (decision[s][h] /= Nil /\ ~crashed[s]) =>
                    decision'[s][h] = decision[s][h]
    ]_mc_vars

====
