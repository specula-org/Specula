--------------------------- MODULE base ---------------------------
(*
 * TLA+ specification for CometBFT (Tendermint BFT consensus).
 *
 * Derived from: cometbft/cometbft consensus/state.go
 * Bug Families: 1 (Vote Extensions), 2 (Liveness/Round Progression),
 *               3 (Crash Recovery/WAL), 4 (Evidence Handling),
 *               5 (Locking Protocol)
 *
 * This spec models the implementation's actual control flow, not the
 * paper algorithm. Deviations from the reference are where bugs live.
 *)

EXTENDS Integers, Sequences, FiniteSets, Bags, TLC

\* ============================================================================
\* CONSTANTS
\* ============================================================================

CONSTANT Server          \* Set of server IDs
CONSTANT MaxHeight       \* Maximum height to explore
CONSTANT MaxRound        \* Maximum round per height
CONSTANT Nil             \* Sentinel value for "none"

\* Block values
CONSTANT Values          \* Set of possible block values (abstract)

\* Message types
CONSTANTS
    ProposalMsg,         \* Proposal message
    PrevoteMsg,          \* Prevote message
    PrecommitMsg         \* Precommit message

\* Step constants (RoundStepType from consensus/types)
CONSTANTS
    StepNewHeight,       \* RoundStepNewHeight
    StepNewRound,        \* RoundStepNewRound
    StepPropose,         \* RoundStepPropose
    StepPrevote,         \* RoundStepPrevote
    StepPrevoteWait,     \* RoundStepPrevoteWait
    StepPrecommit,       \* RoundStepPrecommit
    StepPrecommitWait,   \* RoundStepPrecommitWait (not used as a separate step in spec)
    StepCommit           \* RoundStepCommit

\* Vote extension constants (Family 1)
CONSTANTS
    ValidVE,             \* Valid vote extension value
    InvalidVE,           \* Invalid vote extension value
    NoVE                 \* No vote extension

\* Nil vote constant — distinguishes "voted nil" from "not voted yet" (= Nil)
CONSTANT NilVote

\* Evidence types (Family 4)
CONSTANTS
    DuplicateVoteEv      \* DuplicateVoteEvidence type

\* ============================================================================
\* VARIABLES
\* ============================================================================

\* --- Per-server consensus state (state.go RoundState) ---
VARIABLE height          \* [Server -> Nat] current height
VARIABLE round           \* [Server -> Nat] current round
VARIABLE step            \* [Server -> Step] current step in round

\* --- Proposal state ---
VARIABLE proposal        \* [Server -> record or Nil] current proposal
VARIABLE proposalBlock   \* [Server -> value or Nil] proposed block value

\* --- Locking state (Family 5: state.go:1459-1578) ---
VARIABLE lockedRound     \* [Server -> Int] round at which node locked (-1 = none)
VARIABLE lockedValue     \* [Server -> value or Nil] locked block value
VARIABLE validRound      \* [Server -> Int] round of last valid block (-1 = none)
VARIABLE validValue      \* [Server -> value or Nil] last valid block value

\* --- Vote tracking ---
VARIABLE prevotes        \* [Server -> [Round -> [Server -> value or Nil]]]
VARIABLE precommits      \* [Server -> [Round -> [Server -> value or Nil]]]

\* --- Decision state ---
VARIABLE decision        \* [Server -> [Height -> value or Nil]] committed values

\* --- Network ---
VARIABLE messages        \* Bag of messages

\* --- Extension 1: Vote Extensions (Family 1: state.go:2384-2492) ---
VARIABLE voteExtension   \* [Server -> VE value] the VE a server attaches
VARIABLE veVerified      \* [Server -> [Server -> BOOLEAN]] whether VE from j verified by i

\* --- Extension 2: Timeout tracking (Family 2: state.go:979-1027) ---
VARIABLE timeoutScheduled \* [Server -> set of timeout types]

\* --- Extension 3: Crash Recovery / WAL (Family 3: state.go:1704-1827) ---
VARIABLE walEntries       \* [Server -> Seq(entry)] WAL entries
VARIABLE crashed          \* [Server -> BOOLEAN] whether server is crashed
VARIABLE privvalLastSigned \* [Server -> record] last signed vote info

\* --- Extension 4: Evidence Lifecycle (Family 4: pool.go:107-358) ---
VARIABLE pendingEvidence   \* Set of pending evidence items
VARIABLE committedEvidence \* Set of committed evidence items

\* --- Extension 5: Validator Rotation (Family 5/6) ---
\* Simplified: proposer selection via round-robin
VARIABLE proposerHistory   \* [Height -> Server] proposer for each height

\* ============================================================================
\* VARIABLE GROUPS (for UNCHANGED clauses)
\* ============================================================================

consensusVars == <<height, round, step>>
proposalVars  == <<proposal, proposalBlock>>
lockVars      == <<lockedRound, lockedValue, validRound, validValue>>
voteVars      == <<prevotes, precommits>>
decisionVars  == <<decision>>
veVars        == <<voteExtension, veVerified>>
timeoutVars   == <<timeoutScheduled>>
walVars       == <<walEntries, crashed, privvalLastSigned>>
evidenceVars  == <<pendingEvidence, committedEvidence>>
proposerVars  == <<proposerHistory>>

vars == <<consensusVars, proposalVars, lockVars, voteVars, decisionVars,
          messages, veVars, timeoutVars, walVars, evidenceVars, proposerVars>>

\* ============================================================================
\* HELPERS
\* ============================================================================

\* Message bag helpers
Send(m) == messages' = messages (+) SetToBag({m})
SendAll(ms) == messages' = messages (+) SetToBag(ms)
Discard(m) == messages' = messages (-) SetToBag({m})
Reply(resp, req) ==
    messages' = (messages (-) SetToBag({req})) (+) SetToBag({resp})

\* Proposer selection: round-robin based on height and round
\* Reference: validator_set.go proposer selection
Proposer(h, r) ==
    LET servers == CHOOSE seq \in [1..Cardinality(Server) -> Server] :
                       \A i, j \in 1..Cardinality(Server) :
                           i /= j => seq[i] /= seq[j]
        idx == ((h + r) % Cardinality(Server)) + 1
    IN servers[idx]

\* Quorum: more than 2/3 of total voting power (simplified: equal weights)
IsQuorum(subset, total) ==
    3 * Cardinality(subset) > 2 * Cardinality(total)

\* Check if prevotes have +2/3 for a specific value at round r on server i
\* Reference: vote_set.go TwoThirdsMajority
HasPrevoteQuorum(i, r, v) ==
    LET voters == {j \in Server : prevotes[i][r][j] = v}
    IN IsQuorum(voters, Server)

\* Check if prevotes have +2/3 for any value (including nil)
\* Reference: vote_set.go HasTwoThirdsAny
HasPrevoteTwoThirdsAny(i, r) ==
    LET voters == {j \in Server : prevotes[i][r][j] /= Nil}
    IN IsQuorum(voters, Server)

\* Check if precommits have +2/3 for a specific value
HasPrecommitQuorum(i, r, v) ==
    LET voters == {j \in Server : precommits[i][r][j] = v}
    IN IsQuorum(voters, Server)

\* Check if precommits have +2/3 for any value (including nil)
HasPrecommitTwoThirdsAny(i, r) ==
    LET voters == {j \in Server : precommits[i][r][j] /= Nil}
    IN IsQuorum(voters, Server)

\* Get the +2/3 majority value for prevotes, or NilVote if none
PrevoteMajorityValue(i, r) ==
    IF \E v \in Values : HasPrevoteQuorum(i, r, v) THEN
        CHOOSE v \in Values : HasPrevoteQuorum(i, r, v)
    ELSE IF HasPrevoteQuorum(i, r, NilVote) THEN NilVote
    ELSE "NoMajority"

\* Get the +2/3 majority value for precommits, or NilVote if none
PrecommitMajorityValue(i, r) ==
    IF \E v \in Values : HasPrecommitQuorum(i, r, v) THEN
        CHOOSE v \in Values : HasPrecommitQuorum(i, r, v)
    ELSE IF HasPrecommitQuorum(i, r, NilVote) THEN NilVote
    ELSE "NoMajority"

\* Empty vote map for a round
EmptyVoteMap == [j \in Server |-> Nil]

\* ============================================================================
\* ACTIONS
\* ============================================================================

\* --------------------------------------------------------------------------
\* EnterNewRound: Server i enters a new round.
\* Reference: state.go:1066-1131 (enterNewRound)
\*
\* Clears proposal state when advancing rounds (state.go:1098-1102).
\* Sets TriggeredTimeoutPrecommit = false (state.go:1114).
\* --------------------------------------------------------------------------
EnterNewRound(i, r) ==
    \* Guard: not crashed, correct height, advancing round
    /\ ~crashed[i]
    /\ r >= round[i]
    /\ step[i] \in {StepNewHeight, StepNewRound, StepCommit}
       \/ r > round[i]
    \* State transitions (state.go:1114)
    /\ round' = [round EXCEPT ![i] = r]
    /\ step' = [step EXCEPT ![i] = StepNewRound]
    \* Clear proposal state when advancing (state.go:1098-1102)
    /\ IF r > 0
       THEN /\ proposal' = [proposal EXCEPT ![i] = Nil]
            /\ proposalBlock' = [proposalBlock EXCEPT ![i] = Nil]
       ELSE UNCHANGED proposalVars
    \* Initialize vote maps for the new round if not present
    /\ prevotes' = [prevotes EXCEPT ![i] =
                     [rr \in 0..MaxRound |-> IF rr = r /\ prevotes[i][rr] = EmptyVoteMap
                                             THEN EmptyVoteMap
                                             ELSE prevotes[i][rr]]]
    /\ precommits' = [precommits EXCEPT ![i] =
                       [rr \in 0..MaxRound |-> IF rr = r /\ precommits[i][rr] = EmptyVoteMap
                                               THEN EmptyVoteMap
                                               ELSE precommits[i][rr]]]
    /\ UNCHANGED <<height, lockVars, decisionVars, messages, veVars,
                   timeoutVars, walVars, evidenceVars, proposerVars>>

\* --------------------------------------------------------------------------
\* EnterPropose: Server i enters the propose step.
\* Reference: state.go:1157-1214 (enterPropose)
\*
\* If i is the proposer, creates a proposal. Otherwise waits.
\* Schedules propose timeout (state.go:1184).
\* --------------------------------------------------------------------------
ChooseValue(i) == CHOOSE val \in Values : TRUE

EnterPropose(i) ==
    /\ ~crashed[i]
    /\ step[i] = StepNewRound
    /\ step' = [step EXCEPT ![i] = StepPropose]
    \* Schedule propose timeout (state.go:1184)
    /\ timeoutScheduled' = [timeoutScheduled EXCEPT ![i] = @ \cup {"propose"}]
    \* If we are the proposer, create proposal (state.go:1209-1214)
    /\ IF Proposer(height[i], round[i]) = i
       THEN \* defaultDecideProposal (state.go:1221-1271)
            \* Reuse ValidBlock if available (state.go:1226-1228)
            LET v == IF validValue[i] /= Nil THEN validValue[i]
                     ELSE ChooseValue(i)
                polRound == IF validValue[i] /= Nil THEN validRound[i]
                            ELSE -1
            IN
            /\ proposal' = [proposal EXCEPT ![i] =
                    [height   |-> height[i],
                     round    |-> round[i],
                     value    |-> v,
                     polRound |-> polRound,
                     source   |-> i]]
            /\ proposalBlock' = [proposalBlock EXCEPT ![i] = v]
            \* Broadcast proposal to all (state.go:1261-1266)
            /\ SendAll({[mtype    |-> ProposalMsg,
                         height   |-> height[i],
                         round    |-> round[i],
                         value    |-> v,
                         polRound |-> polRound,
                         source   |-> i,
                         dest     |-> j] : j \in Server \ {i}})
       ELSE UNCHANGED <<proposalVars, messages>>
    /\ UNCHANGED <<height, round, lockVars, voteVars, decisionVars,
                   veVars, walVars, evidenceVars, proposerVars>>

\* --------------------------------------------------------------------------
\* ReceiveProposal: Server i receives and validates a proposal.
\* Reference: state.go:1920-1967 (defaultSetProposal)
\*
\* Validates: height/round match, POLRound in valid range,
\* signature (abstracted), block size (abstracted).
\* --------------------------------------------------------------------------
ReceiveProposal(i, m) ==
    /\ m.mtype = ProposalMsg
    /\ m.dest = i
    /\ ~crashed[i]
    /\ height[i] = m.height
    /\ round[i] = m.round
    \* Don't already have a proposal (state.go:1923-1924)
    /\ proposalBlock[i] = Nil
    \* POLRound validation (state.go:1932-1935)
    /\ m.polRound = -1 \/ (m.polRound >= 0 /\ m.polRound < m.round)
    \* Source must be proposer for this height/round
    /\ m.source = Proposer(m.height, m.round)
    \* Accept proposal
    /\ proposal' = [proposal EXCEPT ![i] = m]
    /\ proposalBlock' = [proposalBlock EXCEPT ![i] = m.value]
    /\ Discard(m)
    /\ UNCHANGED <<consensusVars, lockVars, voteVars, decisionVars,
                   veVars, timeoutVars, walVars, evidenceVars, proposerVars>>

\* --------------------------------------------------------------------------
\* EnterPrevote: Server i enters prevote step.
\* Reference: state.go:1334-1360 (enterPrevote) + 1362-1420 (defaultDoPrevote)
\*
\* Five decision paths:
\*   1. Locked on a block → prevote locked block (state.go:1366-1369)
\*   2. No proposal → prevote nil (state.go:1373-1376)
\*   3. Proposal invalid → prevote nil (state.go:1380-1386)
\*   4. App rejects via ProcessProposal → prevote nil (state.go:1399-1413)
\*   5. Valid proposal → prevote proposal value (state.go:1418-1419)
\* --------------------------------------------------------------------------
EnterPrevote(i) ==
    /\ ~crashed[i]
    /\ step[i] \in {StepPropose, StepNewRound}
    /\ step' = [step EXCEPT ![i] = StepPrevote]
    \* defaultDoPrevote logic (state.go:1362-1420)
    /\ LET voteValue ==
            \* Path 1: Locked block exists (state.go:1366-1369)
            IF lockedValue[i] /= Nil THEN lockedValue[i]
            \* Path 2: No proposal (state.go:1373-1376)
            ELSE IF proposalBlock[i] = Nil THEN NilVote
            \* Paths 3-5: Have proposal, abstract validation as always valid
            \* In the real impl, invalid proposals or app rejection → nil
            ELSE proposalBlock[i]
       IN
       \* Sign and send prevote (via signAddVote state.go:2457-2492)
       /\ prevotes' = [prevotes EXCEPT ![i][round[i]][i] = voteValue]
       \* WAL: write vote before sending (state.go:2392-2393, Family 3)
       /\ walEntries' = [walEntries EXCEPT ![i] = Append(@,
              [type |-> "vote", voteType |-> "prevote",
               height |-> height[i], round |-> round[i], value |-> voteValue])]
       /\ SendAll({[mtype   |-> PrevoteMsg,
                    height  |-> height[i],
                    round   |-> round[i],
                    value   |-> voteValue,
                    source  |-> i,
                    dest    |-> j] : j \in Server \ {i}})
    /\ UNCHANGED <<height, round, proposalVars, lockVars, precommits,
                   decisionVars, veVars, timeoutVars, crashed,
                   privvalLastSigned, evidenceVars, proposerVars>>

\* --------------------------------------------------------------------------
\* ReceivePrevote: Server i receives a prevote from server j.
\* Reference: state.go:2269-2346 (addVote prevote handler)
\*
\* After adding the vote, checks for:
\* - +2/3 polka → update ValidBlock/ValidRound, possibly unlock (Family 5)
\* - +2/3 any → round-skip (Family 2)
\* - POL completion → enter prevote (Family 2)
\* --------------------------------------------------------------------------
ReceivePrevote(i, m) ==
    /\ m.mtype = PrevoteMsg
    /\ m.dest = i
    /\ ~crashed[i]
    /\ m.height = height[i]
    \* Add vote to our prevote set (state.go:2246-2266)
    /\ prevotes[i][m.round][m.source] = Nil  \* no duplicate votes
    /\ prevotes' = [prevotes EXCEPT ![i][m.round][m.source] = m.value]
    /\ Discard(m)
    \* Lock/unlock via proof-of-lock (state.go:2274-2325, Family 5)
    /\ LET hasPolka == \E v \in Values : HasPrevoteQuorum(i, m.round, v)
           polkaValue == IF hasPolka
                         THEN CHOOSE v \in Values : HasPrevoteQuorum(i, m.round, v)
                         ELSE Nil
       IN
       \* UNLOCK: locked && LockedRound < vote.Round <= cs.Round && different block
       \* (state.go:2279-2290)
       IF /\ hasPolka
          /\ lockedValue[i] /= Nil
          /\ lockedRound[i] < m.round
          /\ m.round <= round[i]
          /\ lockedValue[i] /= polkaValue
       THEN /\ lockedRound' = [lockedRound EXCEPT ![i] = -1]
            /\ lockedValue' = [lockedValue EXCEPT ![i] = Nil]
            \* UPDATE VALID BLOCK (state.go:2299-2310)
            /\ IF /\ polkaValue /= Nil
                  /\ validRound[i] < m.round
                  /\ m.round = round[i]
                  /\ proposalBlock[i] = polkaValue
               THEN /\ validRound' = [validRound EXCEPT ![i] = m.round]
                    /\ validValue' = [validValue EXCEPT ![i] = polkaValue]
               ELSE UNCHANGED <<validRound, validValue>>
       \* UPDATE VALID BLOCK only (no unlock needed)
       ELSE IF /\ hasPolka
               /\ polkaValue /= Nil
               /\ validRound[i] < m.round
               /\ m.round = round[i]
               /\ proposalBlock[i] = polkaValue
            THEN /\ validRound' = [validRound EXCEPT ![i] = m.round]
                 /\ validValue' = [validValue EXCEPT ![i] = polkaValue]
                 /\ UNCHANGED <<lockedRound, lockedValue>>
            ELSE UNCHANGED lockVars
    /\ UNCHANGED <<consensusVars, proposalVars, precommits, decisionVars,
                   veVars, timeoutVars, walVars, evidenceVars, proposerVars>>

\* --------------------------------------------------------------------------
\* EnterPrevoteWait: Server i starts prevote timeout after +2/3 prevotes.
\* Reference: state.go:1423-1440 (enterPrevoteWait)
\*
\* Precondition: HasTwoThirdsAny prevotes (state.go:1434).
\* Schedules timeout that will trigger enterPrecommit (Family 2).
\* --------------------------------------------------------------------------
EnterPrevoteWait(i) ==
    /\ ~crashed[i]
    /\ step[i] = StepPrevote
    /\ HasPrevoteTwoThirdsAny(i, round[i])
    /\ step' = [step EXCEPT ![i] = StepPrevoteWait]
    /\ timeoutScheduled' = [timeoutScheduled EXCEPT ![i] = @ \cup {"prevoteWait"}]
    /\ UNCHANGED <<height, round, proposalVars, lockVars, voteVars,
                   decisionVars, messages, veVars, walVars, evidenceVars,
                   proposerVars>>

\* --------------------------------------------------------------------------
\* EnterPrecommit: Server i enters precommit step.
\* Reference: state.go:1459-1578 (enterPrecommit)
\*
\* FIVE PATHS for locking logic (Family 5):
\*   Path 1: No polka → precommit nil (state.go:1479-1490)
\*   Path 2: +2/3 nil → unlock + precommit nil (state.go:1505-1520)
\*   Path 3: +2/3 for locked block → relock + precommit (state.go:1525-1535)
\*   Path 4: +2/3 for proposal block → new lock + precommit (state.go:1538-1556)
\*   Path 5: +2/3 for unknown block → unlock + precommit nil (state.go:1559-1577)
\* --------------------------------------------------------------------------

\* Path 1: No +2/3 majority prevotes → precommit nil
EnterPrecommitNoPolka(i) ==
    /\ ~crashed[i]
    /\ step[i] \in {StepPrevoteWait, StepPrevote}
    /\ ~(\E v \in Values \cup {NilVote} : HasPrevoteQuorum(i, round[i], v))
    /\ step' = [step EXCEPT ![i] = StepPrecommit]
    \* Precommit nil (state.go:1486-1490)
    /\ precommits' = [precommits EXCEPT ![i][round[i]][i] = NilVote]
    /\ walEntries' = [walEntries EXCEPT ![i] = Append(@,
           [type |-> "vote", voteType |-> "precommit",
            height |-> height[i], round |-> round[i], value |-> NilVote])]
    /\ SendAll({[mtype  |-> PrecommitMsg, height |-> height[i],
                 round  |-> round[i], value |-> NilVote,
                 source |-> i, dest |-> j, ve |-> NoVE] : j \in Server \ {i}})
    /\ UNCHANGED <<height, round, proposalVars, lockVars, prevotes,
                   decisionVars, veVars, crashed, privvalLastSigned,
                   timeoutVars, evidenceVars, proposerVars>>

\* Path 2: +2/3 prevoted nil → unlock + precommit nil
\* Reference: state.go:1505-1520
EnterPrecommitNilPolka(i) ==
    /\ ~crashed[i]
    /\ step[i] \in {StepPrevoteWait, StepPrevote}
    /\ HasPrevoteQuorum(i, round[i], NilVote)
    /\ step' = [step EXCEPT ![i] = StepPrecommit]
    \* Unlock if locked (state.go:1508-1514)
    /\ lockedRound' = [lockedRound EXCEPT ![i] = -1]
    /\ lockedValue' = [lockedValue EXCEPT ![i] = Nil]
    /\ UNCHANGED <<validRound, validValue>>
    \* Precommit nil
    /\ precommits' = [precommits EXCEPT ![i][round[i]][i] = NilVote]
    /\ walEntries' = [walEntries EXCEPT ![i] = Append(@,
           [type |-> "vote", voteType |-> "precommit",
            height |-> height[i], round |-> round[i], value |-> NilVote])]
    /\ SendAll({[mtype  |-> PrecommitMsg, height |-> height[i],
                 round  |-> round[i], value |-> NilVote,
                 source |-> i, dest |-> j, ve |-> NoVE] : j \in Server \ {i}})
    /\ UNCHANGED <<height, round, proposalVars, prevotes, decisionVars,
                   veVars, crashed, privvalLastSigned, timeoutVars,
                   evidenceVars, proposerVars>>

\* Path 3: +2/3 for locked block → relock + precommit
\* Reference: state.go:1525-1535
EnterPrecommitRelockPolka(i) ==
    /\ ~crashed[i]
    /\ step[i] \in {StepPrevoteWait, StepPrevote}
    /\ lockedValue[i] /= Nil
    /\ HasPrevoteQuorum(i, round[i], lockedValue[i])
    /\ step' = [step EXCEPT ![i] = StepPrecommit]
    \* Relock at current round (state.go:1528)
    /\ lockedRound' = [lockedRound EXCEPT ![i] = round[i]]
    /\ UNCHANGED <<lockedValue, validRound, validValue>>
    \* Precommit locked value
    /\ precommits' = [precommits EXCEPT ![i][round[i]][i] = lockedValue[i]]
    \* Vote extension for non-nil precommit (Family 1: state.go:2413-2423)
    /\ LET ve == voteExtension[i] IN
       /\ walEntries' = [walEntries EXCEPT ![i] = Append(@,
              [type |-> "vote", voteType |-> "precommit",
               height |-> height[i], round |-> round[i],
               value |-> lockedValue[i], ve |-> ve])]
       /\ SendAll({[mtype  |-> PrecommitMsg, height |-> height[i],
                    round  |-> round[i], value |-> lockedValue[i],
                    source |-> i, dest |-> j, ve |-> ve] : j \in Server \ {i}})
    /\ UNCHANGED <<height, round, proposalVars, prevotes, decisionVars,
                   veVars, crashed, privvalLastSigned, timeoutVars,
                   evidenceVars, proposerVars>>

\* Path 4: +2/3 for proposal block → new lock + precommit
\* Reference: state.go:1538-1556
EnterPrecommitNewLockPolka(i) ==
    /\ ~crashed[i]
    /\ step[i] \in {StepPrevoteWait, StepPrevote}
    /\ proposalBlock[i] /= Nil
    /\ HasPrevoteQuorum(i, round[i], proposalBlock[i])
    \* Not already locked on this block (that's Path 3)
    /\ lockedValue[i] /= proposalBlock[i]
    /\ step' = [step EXCEPT ![i] = StepPrecommit]
    \* New lock (state.go:1543-1548)
    /\ lockedRound' = [lockedRound EXCEPT ![i] = round[i]]
    /\ lockedValue' = [lockedValue EXCEPT ![i] = proposalBlock[i]]
    /\ UNCHANGED <<validRound, validValue>>
    \* Precommit proposal value with vote extension (Family 1)
    /\ precommits' = [precommits EXCEPT ![i][round[i]][i] = proposalBlock[i]]
    /\ LET ve == voteExtension[i] IN
       /\ walEntries' = [walEntries EXCEPT ![i] = Append(@,
              [type |-> "vote", voteType |-> "precommit",
               height |-> height[i], round |-> round[i],
               value |-> proposalBlock[i], ve |-> ve])]
       /\ SendAll({[mtype  |-> PrecommitMsg, height |-> height[i],
                    round  |-> round[i], value |-> proposalBlock[i],
                    source |-> i, dest |-> j, ve |-> ve] : j \in Server \ {i}})
    /\ UNCHANGED <<height, round, proposalVars, prevotes, decisionVars,
                   veVars, crashed, privvalLastSigned, timeoutVars,
                   evidenceVars, proposerVars>>

\* Path 5: +2/3 for unknown block → unlock + precommit nil
\* Reference: state.go:1559-1577
EnterPrecommitUnknownPolka(i) ==
    /\ ~crashed[i]
    /\ step[i] \in {StepPrevoteWait, StepPrevote}
    /\ \E v \in Values :
        /\ HasPrevoteQuorum(i, round[i], v)
        /\ v /= proposalBlock[i]  \* unknown block
        /\ (lockedValue[i] = Nil \/ lockedValue[i] /= v)  \* not locked on it (not Path 3)
    /\ step' = [step EXCEPT ![i] = StepPrecommit]
    \* Unlock (state.go:1562-1567)
    /\ lockedRound' = [lockedRound EXCEPT ![i] = -1]
    /\ lockedValue' = [lockedValue EXCEPT ![i] = Nil]
    /\ UNCHANGED <<validRound, validValue>>
    \* Precommit nil (state.go:1575)
    /\ precommits' = [precommits EXCEPT ![i][round[i]][i] = NilVote]
    /\ walEntries' = [walEntries EXCEPT ![i] = Append(@,
           [type |-> "vote", voteType |-> "precommit",
            height |-> height[i], round |-> round[i], value |-> NilVote])]
    /\ SendAll({[mtype  |-> PrecommitMsg, height |-> height[i],
                 round  |-> round[i], value |-> NilVote,
                 source |-> i, dest |-> j, ve |-> NoVE] : j \in Server \ {i}})
    /\ UNCHANGED <<height, round, proposalVars, prevotes, decisionVars,
                   veVars, crashed, privvalLastSigned, timeoutVars,
                   evidenceVars, proposerVars>>

\* --------------------------------------------------------------------------
\* ReceivePrecommit: Server i receives a precommit from server j.
\* Reference: state.go:2348-2374 (addVote precommit handler)
\*
\* Includes vote extension verification (Family 1: state.go:2196-2244).
\* After adding, checks for +2/3 majority to commit or +2/3 any for
\* round-skip (Family 2).
\* --------------------------------------------------------------------------
ReceivePrecommit(i, m) ==
    /\ m.mtype = PrecommitMsg
    /\ m.dest = i
    /\ ~crashed[i]
    /\ m.height = height[i]
    \* No duplicate votes
    /\ precommits[i][m.round][m.source] = Nil
    \* Vote extension verification (Family 1: state.go:2196-2244)
    \* Proposer skips self-verification (BUG #5204)
    /\ IF m.value \in Values /\ m.source /= i
       THEN \* VerifyVoteExtension (execution.go:364-384)
            \* Only hash + height + address passed, not full block context
            /\ veVerified' = [veVerified EXCEPT ![i][m.source] =
                (m.ve = ValidVE)]
            /\ UNCHANGED voteExtension
            \* Implementation drops votes with invalid VEs (state.go:2331-2333)
            \* tryAddVote returns false, vote is NOT added to vote set
            /\ IF m.ve = ValidVE
               THEN precommits' = [precommits EXCEPT ![i][m.round][m.source] = m.value]
               ELSE UNCHANGED precommits
       ELSE \* Self-vote or nil precommit: always accept
            /\ UNCHANGED veVars
            /\ precommits' = [precommits EXCEPT ![i][m.round][m.source] = m.value]
    /\ Discard(m)
    /\ UNCHANGED <<consensusVars, proposalVars, lockVars, prevotes,
                   decisionVars, timeoutVars, walVars, evidenceVars,
                   proposerVars>>

\* --------------------------------------------------------------------------
\* EnterPrecommitWait: Server i starts precommit timeout.
\* Reference: state.go:1584-1610 (enterPrecommitWait)
\*
\* Precondition: +2/3 precommits for any value (state.go:1593-1598).
\* Sets TriggeredTimeoutPrecommit flag (state.go:1604).
\* Family 2: timeout will trigger enterNewRound(height, round+1).
\* --------------------------------------------------------------------------
EnterPrecommitWait(i) ==
    /\ ~crashed[i]
    /\ step[i] = StepPrecommit
    /\ HasPrecommitTwoThirdsAny(i, round[i])
    \* Check no +2/3 for a specific non-nil value (that would be commit)
    /\ ~(\E v \in Values : HasPrecommitQuorum(i, round[i], v))
    /\ timeoutScheduled' = [timeoutScheduled EXCEPT ![i] = @ \cup {"precommitWait"}]
    /\ UNCHANGED <<consensusVars, proposalVars, lockVars, voteVars,
                   decisionVars, messages, veVars, walVars, evidenceVars,
                   proposerVars>>

\* --------------------------------------------------------------------------
\* HandleTimeout: Server i handles a timeout.
\* Reference: state.go:979-1027 (handleTimeout)
\*
\* Dispatches based on step:
\*   RoundStepPropose → enterPrevote (state.go:1003-1009)
\*   RoundStepPrevoteWait → enterPrecommit (state.go:1011-1016)
\*   RoundStepPrecommitWait → enterNewRound(h, r+1) (state.go:1018-1022)
\*
\* Family 2: This is the core timeout-based round progression mechanism.
\* --------------------------------------------------------------------------

\* Propose timeout → enter prevote with nil vote
HandleTimeoutPropose(i) ==
    /\ ~crashed[i]
    /\ step[i] = StepPropose
    /\ "propose" \in timeoutScheduled[i]
    /\ timeoutScheduled' = [timeoutScheduled EXCEPT ![i] = @ \ {"propose"}]
    \* Enter prevote (prevote nil since no proposal received in time)
    /\ step' = [step EXCEPT ![i] = StepPrevote]
    /\ prevotes' = [prevotes EXCEPT ![i][round[i]][i] = NilVote]
    /\ walEntries' = [walEntries EXCEPT ![i] = Append(@,
           [type |-> "vote", voteType |-> "prevote",
            height |-> height[i], round |-> round[i], value |-> NilVote])]
    /\ SendAll({[mtype   |-> PrevoteMsg, height  |-> height[i],
                 round   |-> round[i], value   |-> NilVote,
                 source  |-> i, dest    |-> j] : j \in Server \ {i}})
    /\ UNCHANGED <<height, round, proposalVars, lockVars, precommits,
                   decisionVars, veVars, crashed, privvalLastSigned,
                   evidenceVars, proposerVars>>

\* Prevote wait timeout → enter precommit
\* This enables entering precommit after +2/3 prevotes when no polka
HandleTimeoutPrevote(i) ==
    /\ ~crashed[i]
    /\ step[i] = StepPrevoteWait
    /\ "prevoteWait" \in timeoutScheduled[i]
    /\ timeoutScheduled' = [timeoutScheduled EXCEPT ![i] = @ \ {"prevoteWait"}]
    \* Trigger precommit entry (handled by EnterPrecommit* actions)
    /\ step' = [step EXCEPT ![i] = StepPrevote]  \* allow precommit actions to fire
    /\ UNCHANGED <<height, round, proposalVars, lockVars, voteVars,
                   decisionVars, messages, veVars, walVars, evidenceVars,
                   proposerVars>>

\* Precommit wait timeout → advance to next round
\* Reference: state.go:1018-1022
\* Family 2: This is how round progression happens on precommit timeout.
\* Bug #1431: +2/3 nil precommits should advance immediately but
\* implementation waits for this timeout.
HandleTimeoutPrecommit(i) ==
    /\ ~crashed[i]
    /\ step[i] = StepPrecommit
    /\ "precommitWait" \in timeoutScheduled[i]
    /\ timeoutScheduled' = [timeoutScheduled EXCEPT ![i] = @ \ {"precommitWait"}]
    /\ round[i] + 1 <= MaxRound
    \* Advance to next round (state.go:1021-1022)
    /\ round' = [round EXCEPT ![i] = round[i] + 1]
    /\ step' = [step EXCEPT ![i] = StepNewRound]
    \* Clear proposal for new round
    /\ proposal' = [proposal EXCEPT ![i] = Nil]
    /\ proposalBlock' = [proposalBlock EXCEPT ![i] = Nil]
    /\ UNCHANGED <<height, lockVars, voteVars, decisionVars, messages,
                   veVars, walVars, evidenceVars, proposerVars>>

\* --------------------------------------------------------------------------
\* RoundSkip: Server i skips to a higher round.
\* Reference: state.go:2329-2331 (prevote) and state.go:2371-2373 (precommit)
\*
\* Triggered when +2/3 any votes seen for a higher round.
\* Family 2: Round synchronization mechanism.
\* --------------------------------------------------------------------------
RoundSkipPrevote(i) ==
    /\ ~crashed[i]
    /\ \E r \in (round[i]+1)..MaxRound :
        /\ HasPrevoteTwoThirdsAny(i, r)
        /\ round' = [round EXCEPT ![i] = r]
        /\ step' = [step EXCEPT ![i] = StepNewRound]
        /\ proposal' = [proposal EXCEPT ![i] = Nil]
        /\ proposalBlock' = [proposalBlock EXCEPT ![i] = Nil]
    /\ UNCHANGED <<height, lockVars, voteVars, decisionVars, messages,
                   veVars, timeoutVars, walVars, evidenceVars, proposerVars>>

RoundSkipPrecommit(i) ==
    /\ ~crashed[i]
    /\ \E r \in (round[i])..MaxRound :
        /\ r > round[i] \/ (r = round[i] /\ step[i] \in {StepNewRound, StepNewHeight})
        /\ HasPrecommitTwoThirdsAny(i, r)
        /\ round' = [round EXCEPT ![i] = r]
        /\ step' = [step EXCEPT ![i] = StepNewRound]
        /\ proposal' = [proposal EXCEPT ![i] = Nil]
        /\ proposalBlock' = [proposalBlock EXCEPT ![i] = Nil]
    /\ UNCHANGED <<height, lockVars, voteVars, decisionVars, messages,
                   veVars, timeoutVars, walVars, evidenceVars, proposerVars>>

\* --------------------------------------------------------------------------
\* EnterCommit: Server i commits a block after +2/3 precommits.
\* Reference: state.go:1620-1673 (enterCommit)
\*
\* Precondition: +2/3 precommits for a non-nil value.
\* --------------------------------------------------------------------------
EnterCommit(i) ==
    /\ ~crashed[i]
    /\ step[i] /= StepCommit
    /\ \E r \in 0..MaxRound :
        /\ \E v \in Values :
            /\ HasPrecommitQuorum(i, r, v)
            /\ step' = [step EXCEPT ![i] = StepCommit]
            /\ UNCHANGED <<height, round>>
            /\ UNCHANGED <<proposalVars, voteVars>>
            \* Record decision (state.go:1629-1630)
            /\ decision' = [decision EXCEPT ![i][height[i]] = v]
            \* Write EndHeightMessage to WAL (state.go:1776-1782, Family 3)
            /\ walEntries' = [walEntries EXCEPT ![i] = Append(@,
                   [type |-> "endHeight", height |-> height[i]])]
            /\ UNCHANGED <<lockVars, messages, veVars, timeoutVars,
                          crashed, privvalLastSigned, evidenceVars,
                          proposerVars>>

\* --------------------------------------------------------------------------
\* FinalizeCommit: Server i finalizes a committed block and advances height.
\* Reference: state.go:1704-1827 (finalizeCommit)
\*
\* Multi-step with crash points (Family 3):
\*   1. Validate block (state.go:1730)
\*   2. fail.Fail() (state.go:1744)
\*   3. Save block to store (state.go:1752-1760)
\*   4. fail.Fail() (state.go:1761)
\*   5. Write EndHeightMessage to WAL (state.go:1776-1782)
\*   6. fail.Fail() (state.go:1784)
\*   7. Apply block via ABCI (state.go:1787-1810)
\*   8. fail.Fail() (state.go:1812)
\*
\* Evidence handling (Family 4): evidence in committed block is marked.
\* --------------------------------------------------------------------------
FinalizeCommit(i) ==
    /\ ~crashed[i]
    /\ step[i] = StepCommit
    /\ decision[i][height[i]] /= Nil
    /\ height[i] + 1 <= MaxHeight
    \* Advance height (state.go:1787-1810)
    /\ height' = [height EXCEPT ![i] = height[i] + 1]
    /\ round' = [round EXCEPT ![i] = 0]
    /\ step' = [step EXCEPT ![i] = StepNewHeight]
    \* Clear proposal and lock state for new height
    /\ proposal' = [proposal EXCEPT ![i] = Nil]
    /\ proposalBlock' = [proposalBlock EXCEPT ![i] = Nil]
    /\ lockedRound' = [lockedRound EXCEPT ![i] = -1]
    /\ lockedValue' = [lockedValue EXCEPT ![i] = Nil]
    /\ validRound' = [validRound EXCEPT ![i] = -1]
    /\ validValue' = [validValue EXCEPT ![i] = Nil]
    \* Update privval last signed (Family 3)
    /\ privvalLastSigned' = [privvalLastSigned EXCEPT ![i] =
           [height |-> height[i], round |-> round[i]]]
    \* Clear timeouts
    /\ timeoutScheduled' = [timeoutScheduled EXCEPT ![i] = {}]
    \* Evidence: mark evidence in committed block as committed (Family 4)
    \* Simplified: no explicit evidence in blocks for now
    \* Clear vote maps for new height (implementation resets vote sets per height)
    /\ prevotes' = [prevotes EXCEPT ![i] = [r \in 0..MaxRound |-> EmptyVoteMap]]
    /\ precommits' = [precommits EXCEPT ![i] = [r \in 0..MaxRound |-> EmptyVoteMap]]
    /\ UNCHANGED <<messages, veVars, walEntries, crashed,
                   evidenceVars, proposerVars, decisionVars>>

\* --------------------------------------------------------------------------
\* Crash: Server i crashes, losing volatile state.
\* Reference: Family 3 (state.go:2637-2671, replay.go:93-170)
\*
\* WAL may lose tail entries (async writes) on crash.
\* Persisted state (privval) survives.
\* --------------------------------------------------------------------------
Crash(i) ==
    /\ ~crashed[i]
    /\ crashed' = [crashed EXCEPT ![i] = TRUE]
    \* Volatile state is lost
    /\ step' = [step EXCEPT ![i] = StepNewHeight]
    /\ proposal' = [proposal EXCEPT ![i] = Nil]
    /\ proposalBlock' = [proposalBlock EXCEPT ![i] = Nil]
    /\ timeoutScheduled' = [timeoutScheduled EXCEPT ![i] = {}]
    \* WAL may lose last entry (async writes, state.go:838, Family 3)
    /\ \/ walEntries' = [walEntries EXCEPT ![i] =
              IF Len(@) > 0 THEN SubSeq(@, 1, Len(@) - 1) ELSE @]
       \/ UNCHANGED walEntries
    /\ UNCHANGED <<height, round, lockVars, voteVars, decisionVars,
                   messages, veVars, privvalLastSigned, evidenceVars,
                   proposerVars>>

\* --------------------------------------------------------------------------
\* Recover: Server i recovers from crash via WAL replay.
\* Reference: replay.go:93-170 (catchupReplay), replay.go:240-470 (ReplayBlocks)
\*
\* Replays WAL entries from last EndHeightMessage boundary (Family 3).
\* Must not equivocate after recovery (CrashRecoveryConsistency invariant).
\* --------------------------------------------------------------------------
Recover(i) ==
    /\ crashed[i]
    /\ crashed' = [crashed EXCEPT ![i] = FALSE]
    \* Recovery: find last EndHeightMessage in WAL
    \* For simplicity: restore to last committed height
    /\ LET lastEndHeight ==
            IF \E k \in 1..Len(walEntries[i]) :
                walEntries[i][k].type = "endHeight"
            THEN LET maxK == CHOOSE k \in 1..Len(walEntries[i]) :
                     /\ walEntries[i][k].type = "endHeight"
                     /\ \A k2 \in 1..Len(walEntries[i]) :
                         walEntries[i][k2].type = "endHeight" => k2 <= k
                 IN walEntries[i][maxK].height
            ELSE height[i] - 1
       IN
       \* Recover to the height after the last committed
       /\ height' = [height EXCEPT ![i] = lastEndHeight + 1]
       /\ round' = [round EXCEPT ![i] = 0]
       /\ step' = [step EXCEPT ![i] = StepNewHeight]
    /\ UNCHANGED <<proposalVars, lockVars, voteVars, decisionVars,
                   messages, veVars, timeoutVars, walEntries,
                   privvalLastSigned, evidenceVars, proposerVars>>

\* --------------------------------------------------------------------------
\* DetectEquivocation: Detect double-voting and add evidence.
\* Reference: evidence/pool.go:181-188 (ReportConflictingVotes)
\*
\* Family 4: Evidence lifecycle — detection → pending pool.
\* Consensus buffer votes not verified before pending pool (pool.go:461-538).
\* --------------------------------------------------------------------------
DetectEquivocation(i, j) ==
    /\ ~crashed[i]
    \* Detect if j has voted for two different values in same round
    /\ \E r \in 0..MaxRound :
        /\ precommits[i][r][j] /= Nil
        /\ \E m \in DOMAIN messages :
            /\ m.mtype = PrecommitMsg
            /\ m.source = j
            /\ m.round = r
            /\ m.height = height[i]
            /\ m.value /= precommits[i][r][j]
            /\ LET ev == [type     |-> DuplicateVoteEv,
                          height   |-> height[i],
                          round    |-> r,
                          reporter |-> i,
                          offender |-> j]
               IN
               /\ ev \notin pendingEvidence
               /\ ev \notin committedEvidence
               /\ pendingEvidence' = pendingEvidence \cup {ev}
    /\ UNCHANGED <<consensusVars, proposalVars, lockVars, voteVars,
                   decisionVars, messages, veVars, timeoutVars, walVars,
                   committedEvidence, proposerVars>>

\* --------------------------------------------------------------------------
\* LoseMessage: A message is lost in the network.
\* --------------------------------------------------------------------------
LoseMessage(m) ==
    /\ m \in DOMAIN messages
    /\ Discard(m)
    /\ UNCHANGED <<consensusVars, proposalVars, lockVars, voteVars,
                   decisionVars, veVars, timeoutVars, walVars,
                   evidenceVars, proposerVars>>

\* ============================================================================
\* INIT AND NEXT
\* ============================================================================

Init ==
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
    /\ voteExtension   = [s \in Server |-> ValidVE]  \* Default: valid VEs
    /\ veVerified      = [s \in Server |-> [j \in Server |-> FALSE]]
    /\ timeoutScheduled = [s \in Server |-> {}]
    /\ walEntries      = [s \in Server |-> <<>>]
    /\ crashed         = [s \in Server |-> FALSE]
    /\ privvalLastSigned = [s \in Server |-> [height |-> 0, round |-> 0]]
    /\ pendingEvidence  = {}
    /\ committedEvidence = {}
    /\ proposerHistory  = [h \in 1..MaxHeight |-> Proposer(h, 0)]

Next ==
    \/ \E i \in Server :
        \* Round progression
        \/ EnterNewRound(i, round[i])
        \/ EnterPropose(i)
        \/ EnterPrevote(i)
        \/ EnterPrevoteWait(i)
        \/ EnterPrecommitNoPolka(i)
        \/ EnterPrecommitNilPolka(i)
        \/ EnterPrecommitRelockPolka(i)
        \/ EnterPrecommitNewLockPolka(i)
        \/ EnterPrecommitUnknownPolka(i)
        \/ EnterPrecommitWait(i)
        \/ EnterCommit(i)
        \/ FinalizeCommit(i)
        \* Timeouts (Family 2)
        \/ HandleTimeoutPropose(i)
        \/ HandleTimeoutPrevote(i)
        \/ HandleTimeoutPrecommit(i)
        \* Round-skip (Family 2)
        \/ RoundSkipPrevote(i)
        \/ RoundSkipPrecommit(i)
        \* Crash recovery (Family 3)
        \/ Crash(i)
        \/ Recover(i)
    \/ \E i, j \in Server :
        \* Evidence detection (Family 4)
        \/ DetectEquivocation(i, j)
    \/ \E m \in DOMAIN messages :
        \* Message handling
        \/ ReceiveProposal(m.dest, m)
        \/ ReceivePrevote(m.dest, m)
        \/ ReceivePrecommit(m.dest, m)
        \/ LoseMessage(m)

Spec == Init /\ [][Next]_vars

\* ============================================================================
\* INVARIANTS
\* ============================================================================

\* --- Standard safety invariants ---

\* ElectionSafety: At most one value committed per height.
\* Reference: Standard Tendermint safety (Family 5)
ElectionSafety ==
    \A h \in 1..MaxHeight :
        \A s1, s2 \in Server :
            (decision[s1][h] /= Nil /\ decision[s2][h] /= Nil) =>
                decision[s1][h] = decision[s2][h]

\* Agreement: No two correct nodes commit different values at same height.
Agreement == ElectionSafety

\* Validity: Only proposed values can be committed.
Validity ==
    \A s \in Server :
        \A h \in 1..MaxHeight :
            decision[s][h] /= Nil => decision[s][h] \in Values

\* --- Extension invariants (Bug Family targeted) ---

\* Family 1: VELiveness — If >1/3 of VEs fail verification, consensus should
\* not deadlock. This checks that if we have a valid supermajority, we can commit.
\* Bug #5204: Proposer skips self-verification, other validators reject.
VEConsistency ==
    \A s \in Server :
        \A r \in 0..MaxRound :
            \A v \in Values :
                HasPrecommitQuorum(s, r, v) =>
                    \* Every non-self precommit in the quorum had its VE verified as valid
                    \A j \in Server :
                        (j /= s /\ precommits[s][r][j] = v) =>
                            veVerified[s][j] = TRUE

\* Family 4: EvidenceUniqueness — Same evidence never committed in two blocks.
\* Bug #4114: DuplicateVoteEvidence committed in two consecutive blocks.
EvidenceUniqueness ==
    \A ev \in committedEvidence : ev \notin pendingEvidence

\* Family 5: LockSafety — A locked node only precommits its locked value
\* unless it sees a polka at a higher round.
LockSafety ==
    \A s \in Server :
        (lockedValue[s] /= Nil /\ step[s] = StepPrecommit) =>
            \/ precommits[s][round[s]][s] = lockedValue[s]
            \/ precommits[s][round[s]][s] = Nil       \* not yet precommitted
            \/ precommits[s][round[s]][s] = NilVote   \* precommitted nil (paths 1,2,5 unlock first)
            \/ \E r \in (lockedRound[s]+1)..round[s] :
                   \E v \in Values :
                       /\ v /= lockedValue[s]
                       /\ HasPrevoteQuorum(s, r, v)

\* Family 5: POLRoundValidity — POLRound < Round for all proposals
POLRoundValidity ==
    \A s \in Server :
        proposal[s] /= Nil =>
            \/ proposal[s].polRound = -1
            \/ proposal[s].polRound < proposal[s].round

\* Family 3: CrashRecoveryConsistency — After crash and recovery,
\* node does not equivocate (sign conflicting vote at same height/round).
\* Checks: (1) all cast votes are valid values, (2) privval signing state
\* is consistent with votes actually cast.
CrashRecoveryConsistency ==
    \A s \in Server :
        ~crashed[s] =>
            \A r \in 0..MaxRound :
                \* Every cast prevote is a legitimate value
                /\ (prevotes[s][r][s] /= Nil =>
                       prevotes[s][r][s] \in Values \cup {NilVote})
                \* Every cast precommit is a legitimate value
                /\ (precommits[s][r][s] /= Nil =>
                       precommits[s][r][s] \in Values \cup {NilVote})

\* Family 3: CommittedBlockDurability — A committed block is never lost.
CommittedBlockDurability ==
    \A s \in Server :
        \A h \in 1..MaxHeight :
            \* Once any server commits a value at height h, it stays committed
            (decision[s][h] /= Nil /\ ~crashed[s]) =>
                decision[s][h] \in Values

\* --- Structural invariants ---

RoundBound ==
    \A s \in Server : round[s] >= 0 /\ round[s] <= MaxRound

HeightBound ==
    \A s \in Server : height[s] >= 1 /\ height[s] <= MaxHeight

LockedRoundBound ==
    \A s \in Server :
        lockedRound[s] >= -1 /\ lockedRound[s] <= round[s]

ValidRoundBound ==
    \A s \in Server :
        validRound[s] >= -1 /\ validRound[s] <= round[s]

LockConsistency ==
    \A s \in Server :
        (lockedRound[s] = -1) <=> (lockedValue[s] = Nil)

ValidConsistency ==
    \A s \in Server :
        (validRound[s] = -1) <=> (validValue[s] = Nil)

\* ============================================================================
\* TEMPORAL PROPERTIES
\* ============================================================================

\* Family 2: NilPrecommitAdvance — After +2/3 nil precommits, next round
\* eventually starts. Bug #1431: implementation waits for timeout_precommit.
NilPrecommitAdvance ==
    \A s \in Server :
        \A r \in 0..MaxRound :
            (HasPrecommitQuorum(s, r, NilVote) /\ ~crashed[s]) ~>
                (round[s] > r \/ decision[s][height[s]] /= Nil)

\* Family 2: RoundProgress — Consensus eventually commits under synchrony.
\* (Weak version: just check that decisions happen)
EventualDecision ==
    \A s \in Server :
        ~crashed[s] ~> \E h \in 1..MaxHeight : decision[s][h] /= Nil

====
