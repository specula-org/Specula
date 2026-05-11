# BFT / Byzantine Fault Tolerant Analysis

Use this reference **in addition to** `distributed-analysis.md` when the target is a BFT consensus protocol. `distributed-analysis.md` covers the 6 canonical distributed fault families (crash, message loss, timeout, non-atomic persistence, config change, snapshot) — all of which assume nodes fail in honest, known ways. This file covers **only** what is additional under a Byzantine threat model.

Classify the target as **BFT** if its safety / liveness arguments depend on tolerating ≤ *f* deviating nodes whose behavior is unconstrained beyond cryptographic primitives (i.e., `n ≥ 3f+1` and the threat model includes deliberate protocol violation, not just crash). Examples: PBFT, HotStuff, Tendermint / CometBFT, DiemBFT / AptosBFT, IBFT / QBFT, HoneyBadgerBFT, Algorand BA*, Narwhal+Bullshark.

If the target is purely crash-fault-tolerant (Raft, Multi-Paxos, classic primary-backup), use `distributed-analysis.md` alone — this file does not apply.

---

## 1. Two-Layer Adversary Model

The BFT literature is canonical about the **environment** the adversary operates in, but ad-hoc about the **specific behaviors** it exhibits. Spec generation must follow that separation.

### 1.1 Layer 1: Environment Dimensions

Four orthogonal dimensions. Decide each in the modeling brief's § 1 System Overview before writing any action.

| Dimension | Options | Default for permissioned BFT |
|---|---|---|
| **Corruption type** | static / adaptive / mobile | static (faulty set + keys fixed at init) |
| **Network model** | synchronous / partial-synchronous (post-GST) / asynchronous | partial-synchronous (DLS 1988) |
| **Computational power** | unauthenticated / authenticated + crypto-bounded | authenticated; no honest-signature forgery |
| **Threshold** | `n ≥ 3f+1` / signed-synchronous variants | `f < n/3` |

If the target deviates from any default — e.g. Algorand uses adaptive corruption + cryptographic sortition; HoneyBadgerBFT is asynchronous; stake-weighted PoS systems use weight thresholds — record the deviation explicitly in the brief. Different environments materially change which Layer 2 actions are load-bearing.

**Foundational sources**: Lamport-Shostak-Pease 1980 / 1982 (corruption + threshold); FLP 1985 (asynchrony); Dwork-Lynch-Stockmeyer 1988 (partial synchrony); Castro-Liskov 1999 (authenticated computational model).

### 1.2 Layer 2: Action Categories (9)

The 9 categories below are the modal cluster of Byzantine actions concretized across BFT proofs and testing tools. Use them as a checklist when scoping the brief; skip explicitly any category the target genuinely does not expose.

| # | Category | Default profile |
|---|---|---|
| 2.1 | Equivocation | **baseline** |
| 2.2 | Invalid Content Fabrication | **baseline** |
| 2.3 | Omission / Withholding | **baseline** |
| 2.4 | Selective Dissemination / Censorship | conditional |
| 2.5 | Replay / Stale-Context Misuse | **baseline** |
| 2.6 | State Rollback / Amnesia | **baseline** |
| 2.7 | Certificate / Quorum-Proof Manipulation | **baseline** |
| 2.8 | Evidence / Accountability Lifecycle | conditional |
| 2.9 | Adaptive / Posterior Corruption | conditional |

**Baseline** = must consider and justify; usually high-priority but not mandatory in the first implementation if the brief deliberately scopes it out.
**Conditional** = add only when system-specific evidence justifies (see each category).

---

## 2. Adversary Action Reference

### 2.1 Equivocation

A Byzantine identity signs or sends incompatible protocol messages for the same logical slot (round / height / view / epoch).

- **Applicable when**: every BFT protocol. Equivocation is the single most universal adversary action across PBFT-family literature, Twins, CometBFT accountability (where equivocation is one of the scoped light-client attack classes alongside lunatic and amnesia), and Ethereum slashing rules.
- **Spec hint**: action wrapper `ByzEquivocate(s, r, v1, v2)` with `s ∈ Faulty`, `v1 ≠ v2`, both messages added to the message set in one step. The counterexample of interest is two honest validators committing different values at the same height.
- **Case-study reference**: `case-studies/autobahn/spec/MC.tla` (`MCByzantinePrepare` fires repeatedly with different `val` for the same `(slot, view)` — emergent equivocation).
- **Composition note**: equivocation alone often violates Agreement directly; combined with 5.2 message loss / partition (distributed-analysis.md), it produces classic split-brain.

### 2.2 Invalid Content Fabrication

A Byzantine node emits a syntactically authentic but semantically invalid proposal, header, value, or state-transition (e.g., a block with an invalid execution result, a header pointing at a stale parent, a "lunatic" header from a long-ago epoch).

- **Applicable when**: every BFT protocol with content-validity checks at receivers. Particularly load-bearing for light-client protocols (CometBFT lunatic attack, Algorand block verification) and protocols where the leader's freedom in proposal content is large (HotStuff `pre_prepare`).
- **Spec hint**: `ByzProposeInvalid(s, r, v)` with `s ∈ Faulty` and a `¬ValidValue(v)` precondition. The receiver-side validity predicate must be modeled explicitly — bugs hide where a receiver "trusts" an invalid value.
- **Case-study reference**: `case-studies/autobahn/spec/MC.tla` (`MCByzantinePrepare` with arbitrary `val` — no per-value QC binding, exposed DA-1). `case-studies/cometbft/spec/MC.tla` (`MCInjectInvalidVE` — narrow VE-only fabrication; surfaced bug #5204).
- **Composition note**: composes with 2.5 replay (fabricated content presented in wrong context) and with 2.4 selective dissemination (different validators see different fabricated content).

### 2.3 Omission / Withholding

A Byzantine node suppresses a proposal / vote / commit / certificate that an honest protocol step would have sent.

- **Applicable when**: every BFT protocol. Omission is the minimal liveness-killing behavior. Sometimes folded into the network layer's `LoseMessage`, but **must be modeled as a Byzantine-side action when** the protocol distinguishes "I deliberately didn't send" from "network dropped what I sent" — for example, when accountability rules require evidence of refusal-to-vote (CometBFT) or when the protocol's view-change relies on Byzantine *unable* to silently abstain.
- **Spec hint**: default is implicit — honest send predicates guard on `s ∉ Faulty`, so Faulty nodes simply never emit required messages. No explicit action is needed. Add an explicit `ByzWithhold(s, msgType, r)` action only when accountability requires the protocol layer to observe the refusal (an invariant reads a witness, or a protocol step measures the silence). Without that observation channel, an explicit no-op only inflates state space.
- **Case-study reference**: no corpus example yet. `LoseMessage` (distributed-analysis.md § 5.2) approximates but conflates network drop with adversarial silence.
- **Composition note**: composes with 5.3 Timeout (distributed-analysis.md) to produce liveness violations under partial synchrony.

### 2.4 Selective Dissemination / Censorship

A Byzantine node sends or forwards a message to a chosen subset of peers rather than to all, biasing what different honest nodes observe.

- **Applicable when**: BFT protocols where the safety / liveness argument depends on receivers eventually converging on the same set of certified messages — e.g., HotStuff pacemaker, Tendermint view change, Narwhal/Bullshark certified DAG. **Distinct from 5.2 message loss** (network layer): selective dissemination is a node deciding *who* to send to, message loss is the network deciding *whether* to deliver.
- **Spec hint**: requires a directed message bag rather than a global one. `messages : Set([sender, to: Subset(Server), type, ...])`. Action wrapper `ByzSendSelective(s, r, v, targets)` with `targets ⊆ Server \ {s}`. This is a non-trivial base-spec change — usually the largest engineering cost of adopting this category.
- **Case-study reference**: no corpus example yet. Existing BFT specs use a global message bag; adopting this category requires the directed-bag refactor described in the Spec hint.
- **Composition note**: composes with 2.1 equivocation to produce *targeted* equivocation (different recipients see different sides of the equivocation).
- **Conditional**: add this category when the target's view-change / pacemaker / DAG construction has been historically bug-prone around message-direction semantics. Otherwise the engineering cost of directed bags exceeds the bug-finding return.

### 2.5 Replay / Stale-Context Misuse

A Byzantine node reuses an old but valid signed message in a wrong round / view / height / epoch / period.

- **Applicable when**: every protocol with epoch transitions, view changes, or persistent signed material (QCs, TCs, commit certificates). Particularly load-bearing for reconfiguration spec (membership change boundary), pipelined consensus (HotStuff QC chaining), and PoS finality (Casper FFG surround-vote rules, which are protocol-specific subtypes of replay + state-rollback).
- **Spec hint**: action wrapper `ByzReplay(s, m_old, newCtx)` with `m_old ∈ messages`, `m_old.sender = s ∈ Faulty`, emit `[m_old EXCEPT !.round = newCtx]`. The protocol's freshness checks (view monotonicity, epoch validation) are exactly what determines whether this attack is admissible.
- **Case-study reference**: `case-studies/aptosbft/spec/MC_epoch.tla` (`ReceiveTimeoutWeakEpoch` / `ReceiveOrderVoteWeakEpoch`) — narrow partial example: release-build `debug_assert` bypass on epoch boundary.
- **Composition note**: composes with 5.5 ConfigChange (distributed-analysis.md) to expose epoch-transition fork attacks.

### 2.6 State Rollback / Amnesia

A Byzantine validator signs as if it had lost or discarded prior protocol-relevant state (last vote, lock, highest QC, last finalized height, slashing DB), then signs a conflicting history.

- **Applicable when**: every protocol with per-validator persistent safety state. CometBFT light-client accountability lists amnesia as one of three exhaustive attack classes. Twins implements "lock forgetting" as one of three primary fault-injection patterns. Casper FFG surround-vote rules formalize a specific amnesia subtype.
- **Spec hint**: `ByzAmnesia(s, r, v)` with `s ∈ Faulty` and a precondition referencing `PriorLocks[s]` / `LastVote[s]` from spec history. The wrapper signs the new conflicting message; the safety invariant being violated is typically "no validator signs two votes that surround a finalized checkpoint" or "no validator votes differently after locking on a value".
- **Case-study reference**: no corpus example yet.
- **Composition note**: composes with 5.1 Crash (distributed-analysis.md) — a Byzantine validator can claim its persisted safety state was lost across a (real or claimed) crash. This is the most important composition pattern for Tendermint/HotStuff-family systems.

### 2.7 Certificate / Quorum-Proof Manipulation

A Byzantine actor forges, reuses, or relies on malformed, stale, conflicting, or insufficient QC / TC / commit-certificate / aggregated-signature material. Typically surfaces through gaps in the receiving side's certificate verification (digest computation, threshold check, content binding) — **not** through cryptographic primitive breaks.

- **Applicable when**: every BFT protocol whose safety / liveness invariants are stated in terms of certificates — PBFT prepared/commit certificates, HotStuff QCs and TCs, Tendermint commits, DiemBFT / AptosBFT QC+TC, Narwhal / Bullshark certified DAG blocks. Empirically the most bug-dense category in real BFT implementations: autobahn's DA-1 (QC not bound to value), DA-2 (`Timeout::digest` hashes nothing → forgeable TC), DA-3 (`TC::verify` always Ok), and DA-5 (winning-view selection from wrong cert) are all instances.
- **Spec hint**: two default-safe action shapes — neither forges honest signatures.
  - `ByzForgeCertificate(s, certType, sl, v, val, signers)`: claimed `signers ⊆ Faulty`. The cert is "broken" via wrong value-binding, insufficient quorum, or malformed digest.
  - `ByzReuseRealCertificate(s, cert, val_target)`: Byzantine takes a real existing certificate (signers are honest, they really signed `cert.value`) and presents it as binding a different value. **Value-binding reuse example** — models autobahn DA-1 (QC not bound to value). The template body only mutates `value`; for other stale-context attacks (different slot, view, or epoch), extend the action to mutate the corresponding field. No signature forgery; exploits value-binding / freshness gaps.
  The **receiver-side** verification predicates (`ValidateQC`, `VerifyTC`, `CertSignersIntersect`, value-binding check) are the bug surface — missing or weakened predicates are how attacks succeed. **Verification-bypass variant**: `claimedSigners ⊆ Server` (may include honest IDs) is allowed only when the case study explicitly models a broken receiver-side check (e.g., autobahn DA-3 where `TC::verify` always returns Ok). Outside that scope, the bypass variant models honest-signature forgery and produces spurious bugs.
- **Case-study reference**: `case-studies/autobahn/spec/MC_hunt_safety.tla` (`MCByzantineTimeout` + `MCByzantineVotePrepare` / `MCByzantineVoteConfirm`) — used in `MC_hunt_da23.cfg` to find autobahn DA-2 / DA-3.
- **Composition note**: composes with 2.5 Replay (stale certificate reused in new view) and 2.1 Equivocation (Byzantine assembles conflicting QCs for the same slot/view).

### 2.8 Evidence / Accountability Lifecycle (conditional)

A Byzantine actor creates, censors, duplicates, replays, or races evidence / slashing artifacts in the protocol's accountability subsystem. Distinct from the consensus path itself: evidence governs what the system *records about* Byzantine behavior, not how consensus proceeds.

- **Applicable when**: target has an explicit evidence pool, slashing module, light-client accountability mechanism, or fork-detection subsystem. Tendermint / CometBFT evidence pool, Casper FFG slashing rules, Ethereum proposer/attester slashing, Aptos slashing infrastructure all fit. Permissioned BFT protocols without these subsystems do not need 2.8.
- **Spec hint**: evidence is per-node (`evidencePool[s]`) — Byzantine cannot delete from another node's pool. Realistic action wrappers: `ByzWithholdEvidenceMsg(s, ev)` (don't gossip own evidence), `ByzProposeBadEvidence(s, ev_invalid)` (gossip invalid evidence; receiver-side `ValidEvidence` is the bug surface), `ByzReplayOldEvidence(s, ev_old, newCtx)`, `ByzGossipConflictingEvidence(s, ev_dup)`. Candidate invariants, when supported by the protocol's gossip / expiry / slashing-availability assumptions: "evidence for any committed Byzantine action eventually applies", "no false evidence applies", "evidence-pool monotonic across reconfiguration".
- **Case-study reference**: no corpus example yet. `case-studies/cometbft/spec/base.tla` has `DetectEquivocation` as a reactive-only sink — a starting point but not a full evidence-lifecycle model.
- **Composition note**: composes with 2.1 Equivocation (Byzantine equivocates, then suppresses the resulting evidence) and 2.4 Selective Dissemination (evidence reaches some validators but not others).
- **Conditional**: include when CometBFT-style accountability is in scope. cometbft is the immediate candidate in our corpus.

### 2.9 Adaptive / Posterior Corruption (conditional)

The adversary corrupts a node *after* learning its role (e.g., after a leader is announced, after committee membership is revealed) or *after* historical state exists (e.g., long-range attack via leaked retired-validator keys).

- **Applicable when**: dynamic-committee systems (Algorand BA*), PoS systems with weak-subjectivity windows (Ethereum, Casper), and any protocol whose security argument relies on the secrecy of role assignment. **Not applicable** to permissioned BFT with fixed validator sets (the default 4-case corpus all fit this).
- **Spec hint**: model `Faulty` as a state variable (not a constant); allow `Faulty' = Faulty ∪ {s}` under the threshold `Cardinality(Faulty') × 3 < Cardinality(Server)`. For long-range, require modeling retired-validator key state separately from active state.
- **Case-study reference**: no corpus example yet.
- **Composition note**: composes with 2.5 Replay (corrupted retired validator replays old signed material across an epoch boundary).
- **Conditional**: include only when the target system has dynamic committees, stake-based selection, or long-lived keys with retirement. Permissioned BFT with fixed `n=4` validators does not need this.

---

## 3. Default Adversary Profile

For first-pass BFT spec generation, **consider and justify** each of the 6 baseline categories (2.1, 2.2, 2.3, 2.5, 2.6, 2.7). They are usually high-priority but not mandatory — implement first the smallest set that exercises the case-study hypothesis, and record in the modeling brief which baseline categories are intentionally deferred and why. Additional categories and compositions can be added in later rounds. The conditional categories activate as follows: 2.4 when topology / view-change correctness is in scope; 2.8 when the target has an explicit evidence pool or slashing module; 2.9 when the target uses dynamic committees or stake.

A spec that models only 2.1 + 2.2 ("Byzantine sends arbitrary signed messages") is the floor — sufficient for safety violations of the form "two honest nodes commit different values" but insufficient for liveness, amnesia-after-crash, certificate-forgery, or epoch-boundary bugs.

---

## 4. BFT-Specific Analysis Patterns

These complement the patterns in `distributed-analysis.md` § 2. Use both lists when analyzing a BFT target. **These are prompts, not filters** — if code review reveals a protocol-specific failure mode that does not fit any pattern below, keep it and map it back to the closest category only after analysis, not the other way around.

### 4.1 Validator State Machine Inconsistency Across Roles

Find code paths that should enforce the same safety rule (no double-vote, lock-then-vote, vote-then-persist) but do so inconsistently across validator roles (leader / replica / observer). Maps to category 2.6 amnesia and 2.5 replay.

### 4.2 Certificate / Signature Verification Gaps (not key forgery)

We do not model key forgery, but we **do** model gaps in certificate / digest / signature **verification** — e.g., autobahn DA-3 (`TC::verify` always returns Ok), autobahn DA-2 (`Timeout::digest` hashes nothing). These directly enable category 2.7 (Certificate / Quorum-Proof Manipulation) attacks; the bug surface is the receiver-side validation predicate, not the cryptographic primitive itself.

### 4.3 View-Change / Round-Change Correctness Under Adversarial Timing

The view-change protocol is the most bug-prone subprotocol in BFT systems (autobahn DA-5 winning-view bug; PBFT historical view-change races). Model 2.1 equivocation + 2.5 replay + 5.3 Timeout (distributed-analysis.md) jointly when in this area.

### 4.4 Accountability / Evidence Lifecycle Integrity

Many BFT systems include evidence pools, slashing modules, or light-client checkpoints. Bugs hide in evidence creation (does the system actually create evidence for every detectable Byzantine action?), evidence propagation (can evidence be censored / replayed?), and evidence application (is the slashing transaction itself idempotent?). Model 2.8 + the originating Byzantine action that produces the evidence (usually 2.1 equivocation, 2.2 invalid content, 2.6 amnesia, or a protocol-specific slashing condition).

### 4.5 Light-Client Safety vs Full-Node Safety Divergence

Light clients verify with reduced state and bounded trust. CometBFT's lunatic attack class only matters for light clients. When the target distinguishes full-node from light-client safety, model both — bugs often hide where the light-client verifier diverges from the full-node verifier.

---

## 5. Spec Encoding Pattern

Recommended idiom: **Byzantine subset in the protocol model + per-category MC wrapper actions**. Hybrid of Tendermint-style "Byzantine subset as constant" (a protocol-level concept) + autobahn-style per-category wrappers (an MC-level concept). Counters, when present, live in `MC.tla` as TLC search budgets — they are not part of the Byzantine semantics. The template below makes the split explicit.

**This is a skeleton, not a drop-in adversary.** When adapting it: preserve the target protocol's actual message schema (the placeholder `[sender, type, round, value]` is illustrative — replace it with the protocol's real record shape), preserve local-vs-global state ownership (most BFT systems have per-node state, not global pools), and route every wrapper through the receiver-side validation predicate the protocol actually runs. Instantiate only categories the modeling brief justifies; do not include wrappers for unused categories just because they appear here.

```tla
\* ============================================================
\* BFT Adversary Layer
\*
\* Split between two files:
\*   base.tla — Byzantine subset + unbounded adversary action bodies
\*              (Byzantine semantics, not a budget)
\*   MC.tla   — counter-bounded wrappers around base actions
\*              (TLC search budgets; not part of Byzantine semantics)
\* ============================================================

\* ============================================================
\* PART A: base.tla — Byzantine subset and unbounded actions
\* ============================================================

CONSTANTS
    Server,           \* All replicas
    Faulty,           \* Byzantine subset (static template; for adaptive mode see delta below)
    Value, Round

ASSUME Faulty \subseteq Server
ASSUME 3 * Cardinality(Faulty) < Cardinality(Server)   \* f < n/3

\* Authentication axiom (Velisarios-style).
\* Faulty nodes may sign any message as themselves; honest signatures are
\* unforgeable. Do not model crypto primitive breaks.
SignedBy(m, s)   == m.sender = s
ByzCanSign(s, m) == s \in Faulty /\ SignedBy(m, s)

\* --- 2.1 Equivocation ---
ByzEquivocate(s, r, v1, v2) ==
    /\ s \in Faulty /\ v1 # v2
    /\ messages' = messages \cup
       { [sender |-> s, type |-> "Vote", round |-> r, value |-> v1],
         [sender |-> s, type |-> "Vote", round |-> r, value |-> v2] }
    /\ UNCHANGED state

\* --- 2.2 Invalid content fabrication ---
ByzProposeInvalid(s, r, v) ==
    /\ s \in Faulty /\ ~ValidValue(v)
    /\ messages' = messages \cup
       { [sender |-> s, type |-> "Propose", round |-> r, value |-> v] }
    /\ UNCHANGED state

\* --- 2.3 Omission (default: implicit; no base action) ---
\* Honest send predicates guard on (s \notin Faulty); Faulty nodes simply
\* never emit required messages. Add an explicit `ByzWithhold` base action
\* only when accountability requires the protocol layer to witness the
\* refusal — without an observation channel, an explicit no-op only inflates
\* state space.

\* --- 2.4 Selective Dissemination (conditional; requires directed bag) ---
ByzSendSelective(s, r, v, targets) ==
    /\ s \in Faulty /\ targets \subseteq (Server \ {s})
    /\ messages' = messages \cup
       { [sender |-> s, to |-> targets, type |-> "Vote",
          round |-> r, value |-> v] }
    /\ UNCHANGED state

\* --- 2.5 Replay / stale-context misuse ---
ByzReplay(s, m_old, newCtx) ==
    /\ s \in Faulty
    /\ m_old \in messages /\ m_old.sender = s
    /\ messages' = messages \cup { [m_old EXCEPT !.round = newCtx] }
    /\ UNCHANGED state

\* --- 2.6 State rollback / amnesia ---
ByzAmnesia(s, r, v) ==
    /\ s \in Faulty
    /\ \E priorLock \in PriorLocks[s] :
         v # priorLock.value /\ r >= priorLock.round
    /\ messages' = messages \cup
       { [sender |-> s, type |-> "Vote", round |-> r, value |-> v] }
    /\ UNCHANGED state

\* --- 2.7 Certificate / Quorum-proof manipulation ---
\* Default form: claimed signers ⊆ Faulty (no honest-signature forgery).
\* The cert is "broken" via wrong value-binding, insufficient quorum, or
\* malformed digest — receiver-side ValidateCert / VerifyTC is the bug surface.
ByzForgeCertificate(s, certType, sl, v, val, signers) ==
    /\ s \in Faulty
    /\ certType \in {"QC", "TC", "Commit"}
    /\ signers \subseteq Faulty
    /\ messages' = messages \cup
       { [sender |-> s, type |-> certType, slot |-> sl, view |-> v,
          value |-> val, signers |-> signers] }
    /\ UNCHANGED state

\* Reuse a real existing certificate with the value-binding mutated.
\* Models autobahn DA-1 (QC not bound to value) — a value-binding example.
\* For other stale-context cases (different slot / view / epoch), mutate
\* the corresponding field in the EXCEPT clause. No signature forgery;
\* exploits value-binding / freshness gaps.
ByzReuseRealCertificate(s, cert, val_target) ==
    /\ s \in Faulty
    /\ cert \in ExistingCerts
    /\ messages' = messages \cup
       { [cert EXCEPT !.value = val_target] }
    /\ UNCHANGED state

\* Verification-bypass variant — ONLY when the case study explicitly models
\* a broken receiver-side check (e.g., autobahn DA-3: `TC::verify` always Ok).
\* Without that, this variant models honest-signature forgery and produces
\* spurious bugs.
\*   ByzForgeCertificateClaimAny(s, certType, sl, v, val, claimedSigners) ==
\*     /\ s \in Faulty
\*     /\ certType \in {"QC", "TC", "Commit"}
\*     /\ claimedSigners \subseteq Server   \* may include honest IDs
\*     /\ messages' = messages \cup
\*        { [sender |-> s, type |-> certType, slot |-> sl, view |-> v,
\*           value |-> val, signers |-> claimedSigners] }
\*     /\ UNCHANGED state

\* --- 2.8 Evidence / accountability lifecycle (conditional) ---
\* Evidence is per-node (`evidencePool[s]`) and propagates via gossip,
\* proposal inclusion, or slashing transactions. Byzantine cannot reach
\* into another node's local pool; it can refuse to gossip its own
\* evidence, inject invalid evidence, or race conflicting entries.

ByzWithholdEvidenceMsg(s, ev) ==
    /\ s \in Faulty
    /\ ev \in evidencePool[s]
    /\ UNCHANGED <<messages, state, evidencePool>>

ByzProposeBadEvidence(s, ev_invalid) ==
    /\ s \in Faulty
    /\ ~ValidEvidence(ev_invalid)
    /\ messages' = messages \cup
       { [sender |-> s, type |-> "Evidence", payload |-> ev_invalid] }
    /\ UNCHANGED <<state, evidencePool>>

\* Other realistic actions in this category:
\*   ByzReplayOldEvidence(s, ev_old, newCtx)   — re-gossip stale evidence
\*   ByzGossipConflictingEvidence(s, ev_dup)   — race duplicate entries

\* ============================================================
\* PART B: MC.tla — counter-bounded TLC wrappers
\* (search budgets; not part of Byzantine semantics)
\* ============================================================

CONSTANTS
    MaxByzEquivocate, MaxByzInvalid, MaxByzSelective, MaxByzReplay,
    MaxByzAmnesia, MaxByzCertForge, MaxByzCertReuse, MaxByzEvidence
    \* Set any Max to 0 in a hunt cfg to disable that category cleanly.

VARIABLES byzCounters
\* byzCounters : [equivocate, invalid, selective, replay, amnesia,
\*                cert, certReuse, evidence |-> Nat]
\* Initial:    byzCounters = [equivocate |-> 0, invalid |-> 0, ...]

\* Wrapper pattern: counter check + base action + counter bump.
MCByzEquivocate(s, r, v1, v2) ==
    /\ byzCounters.equivocate < MaxByzEquivocate
    /\ ByzEquivocate(s, r, v1, v2)
    /\ byzCounters' = [byzCounters EXCEPT !.equivocate = @ + 1]

\* The other MC wrappers follow the identical shape; one per category:
\*   MCByzProposeInvalid         — MaxByzInvalid
\*   MCByzSendSelective          — MaxByzSelective
\*   MCByzReplay                 — MaxByzReplay
\*   MCByzAmnesia                — MaxByzAmnesia
\*   MCByzForgeCertificate       — MaxByzCertForge
\*   MCByzReuseRealCertificate   — MaxByzCertReuse
\*   MCByzWithholdEvidenceMsg    — MaxByzEvidence  (shared with next)
\*   MCByzProposeBadEvidence     — MaxByzEvidence  (shared)
\*
\* In adaptive mode (category 2.9), every base action and every MC wrapper
\* must `/\ UNCHANGED Faulty` — otherwise TLC treats Faulty as
\* nondeterministic and silently corrupts new validators outside ByzPromote.
```

### Adaptive-mode delta (category 2.9 only)

When the target requires 2.9 (dynamic committees / PoS / long-range), modify the static template above as follows:

- Move `Faulty` from `CONSTANTS` to `VARIABLES`; initial state `Faulty = InitiallyByzantine` (commonly `{}` for fully adaptive).
- Drop the `ASSUME 3 * Cardinality(Faulty) < Cardinality(Server)` constant assumption; enforce the bound inside the promotion action instead.
- Add a promotion action:

```tla
ByzPromote(s) ==
    /\ s \notin Faulty
    /\ 3 * (Cardinality(Faulty) + 1) < Cardinality(Server)
    /\ Faulty' = Faulty \cup {s}
    /\ UNCHANGED <<messages, state, byzCounters>>
```

- Every base action (`ByzEquivocate`, `ByzProposeInvalid`, …, `ByzProposeBadEvidence`) and every MC wrapper must `/\ UNCHANGED Faulty`. TLC treats unconstrained variables as nondeterministic — without this, any step other than `ByzPromote` would silently corrupt new validators. Their predicates over `Faulty` are read-only; the explicit `UNCHANGED Faulty` is the fix.

For long-range / posterior corruption (key compromise after validator retirement), model the retired-validator key state as a separate variable and allow Byzantine actions on retired identities even after they leave the active `Faulty` set.

### Base-spec dependencies per category

The template references base-spec variables and predicates that are not declared in this skeleton. Before adopting a category, ensure your `base.tla` provides the corresponding dependency:

| Category | Base-spec dependencies |
|---|---|
| 2.1 Equivocation | Message bag schema with `(sender, round, value)` or protocol-equivalent |
| 2.2 Invalid Content | `ValidValue(v)` predicate evaluated at the receiver |
| 2.3 Omission | None (implicit form uses honest-send guard `s ∉ Faulty`) |
| 2.4 Selective Dissemination | Directed message bag: `messages : SUBSET [sender, to: SUBSET Server, ...]` |
| 2.5 Replay | Message schema with a context field (`round` / `view` / `epoch`) checked by the receiver |
| 2.6 State Rollback / Amnesia | Per-validator history: `PriorLocks[s]`, `LastVote[s]`, `LockedQC[s]`, or equivalent |
| 2.7 Certificate Forge / Reuse | Receiver-side `ValidateCert(cert, sender, slot, view, value, signers)`; for `ByzReuseRealCertificate`, also an `ExistingCerts` projection over already-emitted real certificates (e.g., `{m ∈ messages : m.type ∈ {"QC","TC","Commit"}}`) |
| 2.8 Evidence | Per-node pool `evidencePool : [Server -> SUBSET Evidence]` + `ValidEvidence(ev)` predicate |
| 2.9 Adaptive | `Faulty` as VARIABLE; explicit `UNCHANGED Faulty` in every non-`ByzPromote` action |

If your base spec lacks one of these dependencies, either add it (matching the protocol's real semantics) or drop the corresponding adversary category. Do not stub a dependency with a `TRUE` / `SUBSET Server` placeholder — that silently weakens or strengthens the attack and produces unreliable counterexamples.

### Encoding notes

- **Counters are TLC search budgets, not adversary semantics**. The `byzCounters` record and per-category `MaxByz<Category>` constants live in `MC.tla` to bound TLC's exploration of fault-injection actions. They are **not** part of how a Byzantine node behaves in the protocol — a real adversary is not "limited to 3 equivocations". Keep them out of `base.tla`; the base spec should describe Byzantine behavior unbounded.
- **Per-category counters via a `byzCounters` record** — each field has its own `MaxByz<Category>` budget. Hunt cfgs disable a category cleanly by setting its Max to 0; no need for guard plumbing inside each action. Add an optional global `MaxByzTotal` only when you need a cross-category cap.
- **`Faulty` as CONSTANT** in the static-corruption template (the default for permissioned BFT); the adaptive-mode delta above promotes it to a VARIABLE. Pick exactly one form per spec — do not leave both.
- **Authentication via `ByzCanSign`**, not by signature simulation. Specs should never model "Byzantine forges honest signature" — that is a cryptographic break, out of scope by Layer 1 default.
- **Category 2.4 (Selective Dissemination) requires base-spec changes** — message bag becomes directed (`m.to ⊆ Server`). Plan for this when adopting 2.4; the cost is non-trivial.
- **Category 2.8 (Evidence) requires a new per-node state variable** `evidencePool : [Server -> SUBSET Evidence]`. Byzantine actions in this category manipulate gossip messages or their own pool — never another node's local pool directly. Adopt only when the protocol layer models evidence (e.g., cometbft); for protocols without an accountability subsystem, leave 2.8 wrappers out rather than stubbing.

---

## 6. Composition with `distributed-analysis.md`

BFT adversary actions are layered on top of the 6 distributed fault families, not in place of them. The most bug-rich compositions:

| BFT × Distributed | Bug pattern | Reference |
|---|---|---|
| 2.1 Equivocation × 5.2 Partition | Split-brain via targeted double-sign | classical BFT |
| 2.3 Omission × 5.3 Timeout | Liveness attack at view-change boundary | HotStuff pacemaker |
| 2.5 Replay × 5.5 ConfigChange | Stale-cert exploit across epoch boundary | aptosbft `MC_epoch` |
| 2.6 Amnesia × 5.1 Crash | Fork after legitimate restart (double-vote) | aptosbft MC-4 (unmodeled) |
| 2.4 Selective × 5.6 Snapshot | Divergent state catchup view | Tendermint snapshot |
| 2.7 Cert Forge × 5.3 Timeout | Forged TC accepted at view-change boundary | autobahn DA-2/DA-3 |
| 2.7 Cert Forge × 2.1 Equivocation | Conflicting QCs for the same slot | autobahn DA-1 |

Prefer staged analysis when feasible — model and check each family individually before composing, so failures isolate cleanly. But if the hypothesis is inherently cross-family (e.g., aptosbft MC-4 = 2.6 amnesia × 5.1 crash; autobahn DA-2/DA-3 = 2.7 cert-forge × view-change), model the composition directly and document in the brief which component assumptions are being combined. For BFT case studies, this exception overrides the generic "compose only after each family individually passes" guidance in `distributed-analysis.md` § Composition — Byzantine bugs are frequently cross-family by construction, and staged-only modeling will miss them.

---

## 7. What to Avoid

- **Do not** add "twinning" (Twins paper) as a top-level adversary category — it is a fault-injection *mechanism* realizing 2.1 + 2.6 operationally. When a case study uses real twin processes, treat them as the implementation of those two categories, not a new one.
- **Do not** add Ethereum's "surround vote" as a top-level category — model it as a protocol-specific subtype of 2.6 amnesia when the Casper-family target names it. Same pattern for other protocol-specific names: subtype, not top-level.
- **Do not** model cryptographic primitive breaks (signature forgery, hash collision) by default. If the case study is specifically about key compromise, document the exception in the modeling brief's §1.
- **Do not** redefine the 6 distributed fault families. Network loss / partition / reorder / timeout / crash / persistence / config / snapshot all stay in `distributed-analysis.md`. This file is additive only.
- **Do not** enumerate every Byzantine action found in BFT literature. The 9 categories are the modal cluster; per-protocol message-type Byzantine adversaries (autobahn-style `MCByzantinePrepare/Confirm/Commit`) are concrete instances of categories 2.1–2.3 + 2.7, not new top-level actions.

---

## 8. When to Skip This File

- Target is purely crash-fault-tolerant (Raft, Multi-Paxos, primary-backup): use `distributed-analysis.md` alone.
- Target's safety argument explicitly excludes Byzantine threats (some replicated-storage systems, single-writer log-structured systems): use `distributed-analysis.md` alone.
- Target uses BFT consensus for a sub-protocol but the case study is scoped to the non-BFT layer: focus on the relevant layer's threat model, not this file.

If the target layer participates in BFT safety / liveness and you are unsure, use both files; otherwise document in the modeling brief why the BFT layer is out of scope. `bft-analysis.md` adds adversary categories but does not require modeling all 9 if the case study scopes them out explicitly.

