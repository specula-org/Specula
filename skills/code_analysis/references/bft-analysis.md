# BFT / Byzantine Fault Tolerant Analysis

Use this reference **in addition to** `distributed-analysis.md` when the target is a BFT consensus protocol. This file covers what is additional under a Byzantine threat model — vocabulary and reminders, not a prescriptive checklist.

Classify the target as **BFT** if its safety / liveness arguments depend on tolerating ≤ *f* deviating nodes whose behavior is unconstrained beyond cryptographic primitives. Examples: PBFT, HotStuff, Tendermint / CometBFT, DiemBFT / AptosBFT, IBFT / QBFT, HoneyBadgerBFT, Algorand BA*, Narwhal+Bullshark, Tower BFT.

If the target is purely crash-fault-tolerant (Raft, Multi-Paxos, primary-backup), use `distributed-analysis.md` alone — this file does not apply.

> **On examples and case-study names below**: any references to autobahn / aptosbft / cometbft are historical instances illustrating what the vocabulary points at. They are not models to imitate. Each new target deserves a case-specific analysis grounded in its own code, threat model, and the open questions the brief is trying to answer. Do not copy wrapper names, counter shapes, or templates.

---

## 1. Two-Layer Adversary Model

The BFT literature is canonical about the **environment** the adversary operates in, but ad-hoc about the **specific behaviors** it exhibits. Spec generation usually benefits from separating those two concerns.

### 1.1 Layer 1: Environment Dimensions

Four orthogonal dimensions. Record each in the modeling brief's § 1 System Overview before writing any action — the right answer is target-specific, not template-driven.

- **Corruption type**: static / adaptive / mobile. Permissioned BFT typically uses static; Algorand uses adaptive; PoS systems with key retirement need mobile / long-range modeling.
- **Network model**: synchronous / partial-synchronous (post-GST) / asynchronous. Partial-synchronous (DLS 1988) is the default for most production BFT; HoneyBadgerBFT is asynchronous.
- **Computational power**: unauthenticated vs authenticated + crypto-bounded. Almost all production BFT is authenticated with unforgeable honest signatures.
- **Threshold**: `n ≥ 3f+1`, signed-synchronous variants, or stake-weighted thresholds.

If the target deviates from any default, record the deviation explicitly. Different environments materially change which actions are load-bearing.

**Foundational sources**: Lamport-Shostak-Pease 1980 / 1982; FLP 1985; Dwork-Lynch-Stockmeyer 1988; Castro-Liskov 1999.

### 1.2 Layer 2: Action Vocabulary

The labels below are a vocabulary for talking about Byzantine behaviors. They are **not** a checklist; do not assume your target needs all of them, and do not adopt categories that the target's code, threat model, or open questions do not justify.

- **2.1 Equivocation** — signing/sending incompatible messages for the same logical slot.
- **2.2 Invalid content fabrication** — emitting syntactically authentic but semantically invalid proposals / headers / values.
- **2.3 Omission / withholding** — suppressing a proposal / vote / commit / certificate.
- **2.4 Selective dissemination / censorship** — sending to a chosen subset of peers rather than to all.
- **2.5 Replay / stale-context misuse** — reusing an old valid signed message in the wrong round / view / epoch.
- **2.6 State rollback / amnesia** — signing as if persistent safety state (last vote, lock, slashing DB) had been lost or discarded.
- **2.7 Certificate / quorum-proof manipulation** — forging, reusing, or relying on broken QC / TC / commit-cert material. Typically surfaces through receiver-side verification gaps, not crypto breaks.
- **2.8 Evidence / accountability lifecycle** — creating, censoring, duplicating, or racing evidence in the protocol's accountability subsystem (only meaningful if such a subsystem exists).
- **2.9 Adaptive / posterior corruption** — corruption *after* role assignment or via leaked retired-validator keys. Only meaningful for dynamic-committee / PoS-with-retirement systems.

If your target's most realistic Byzantine behavior isn't named above (protocol-specific cryptoeconomic griefing, validator key compromise after retirement, MEV-driven equivocation incentives, vote-lockout-specific deviations in Tower BFT, etc.), describe it directly. The vocabulary is not a closed list.

---

## 2. What Makes a Byzantine Action Worth Modeling

Useful questions to ask of any candidate Byzantine action, regardless of which label it falls under:

- Does the target's code actually expose a check whose failure would admit this behavior? If not, modeling the action explores nothing the protocol layer can see.
- Is the receiver-side validation predicate the bug surface, or the sender-side decision? Most BFT bugs in real implementations live in receiver-side verification (cert validation, freshness checks, value-binding), not in inventing more sender-side mischief.
- Does the action compose with a real-world environmental fault the brief already models (timeout, partition, crash, config change)? Byzantine bugs frequently cross categories — pure Byzantine actions in isolation often reproduce textbook results rather than uncovering new ones.
- Can you state the Phase 4 verdict you predict? If the only honest verdict is "reproduces a known bug that's already fixed", that's the answer-key anti-pattern — drop it. See `modeling-brief-format.md` § 6.1 and `bug-archaeology.md` § 1.4.

---

## 3. Where Bugs Tend to Hide in BFT Implementations

These are prompts for code analysis, not modeling templates. If review reveals a protocol-specific failure mode that does not match any pattern below, keep it.

- **Validator state machine inconsistency across roles** — the same safety rule (no double-vote, lock-then-vote, vote-then-persist) implemented differently for leader / replica / observer.
- **Certificate / signature *verification* gaps** (not key forgery) — receiver-side predicates that always return true, hash functions that hash nothing, digest computations that ignore content, threshold checks that ignore signer identity.
- **View-change / round-change correctness** — historically the most bug-prone subprotocol in BFT systems.
- **Accountability / evidence lifecycle** — evidence creation (does the system create evidence for every detectable Byzantine action?), propagation (can it be censored / replayed?), and application (is slashing idempotent?).
- **Light-client vs full-node safety divergence** — light clients verify with reduced state; bugs hide where the light-client verifier diverges from the full-node verifier.

---

## 4. Spec Encoding — Reminders, Not a Template

When the brief justifies adversary actions, the encoding is target-specific. A few mechanics that tend to come up across BFT specs:

- **`Faulty` as a set of Byzantine identities**. Static threat models keep it a CONSTANT with `3 * Cardinality(Faulty) < Cardinality(Server)`. Adaptive threat models promote it to a VARIABLE — and every other action must then explicitly `UNCHANGED Faulty`, or TLC will silently corrupt new validators outside the promotion action.
- **Authentication axiom**: Byzantine identities sign as themselves; honest signatures are unforgeable. Do **not** model cryptographic primitive breaks unless the case study is specifically about key compromise.
- **Receiver-side validation is the bug surface**. Whatever Byzantine action you write, route it through whatever verification predicate the protocol actually runs (`ValidValue`, `ValidateQC`, `VerifyTC`, `ValidEvidence`, etc.). The wrapper exists so TLC can ask "is this predicate strong enough?"; if you bypass the predicate, the run answers nothing about the implementation.
- **Counters are TLC search budgets, not adversary semantics**. If you bound Byzantine actions, the bounds belong in `MC.tla`, not in `base.tla` — a real adversary is not "limited to 3 equivocations". Each fault-injection action takes its own counter, checked AND incremented on the same transition.
- **Some categories require base-spec changes** rather than just a wrapper. Selective dissemination needs a directed message bag (`m.to ⊆ Server`); evidence lifecycle needs a per-node evidence pool; amnesia needs per-validator history (`PriorLocks`, `LastVote`, etc.) the rest of the spec wouldn't otherwise track. Plan accordingly, or drop the category.

Beyond those mechanics, the right question is not "which category am I checking off?" but "what concrete, open question about my target am I trying to answer?". If you cannot articulate a concrete open question — not anchored to any past commit, fix, or known PR — then there is probably no wrapper worth writing for that category in this case.

### Caveat: no answer-key adversaries

The most common failure mode we've seen in BFT specs is adversaries whose only effect is to reproduce an already-fixed bug — wrappers that, on inspection, amount to `git revert <commit>` in spec form. If you can characterise an adversary action that way, drop it. The MC run produces no information the closed PR didn't already record. Closed PRs are evidence of mechanism bug-proneness, not target lists for the spec to re-enumerate. See `modeling-brief-format.md` § 6.1 (output-value litmus) and `bug-archaeology.md` § 1.4 (value-driven containment).

---

## 5. Composition with `distributed-analysis.md`

BFT adversary actions usually layer on top of the distributed fault vocabulary, not replace it. Byzantine bugs frequently *cross categories* — pure Byzantine actions in isolation often reproduce textbook results, while the practically interesting bugs come from Byzantine behavior composed with timing / partition / crash / config-change.

That said, composition explodes state space and clouds blame attribution, so compose only when the open question requires it. If the hypothesis inherently crosses categories, model the composition directly and document in the brief which components are being combined.

---

## 6. What to Avoid

- **Do not** treat the 9-label vocabulary as a checklist that every BFT target must cover. Each target deserves a case-specific analysis.
- **Do not** copy wrapper names, counter shapes, or schematic templates from other case studies — their design decisions reflect those targets' specific code and threat models.
- **Do not** add protocol-specific Byzantine behaviors as new top-level categories. Twins, surround-votes, lunatic / amnesia attacks, etc., are instances of the existing vocabulary; name them in the brief if the protocol names them, but don't expand the vocabulary list.
- **Do not** model cryptographic primitive breaks by default. If the case study is specifically about key compromise, document the exception in the brief.
- **Do not** stub a required base-spec dependency with a `TRUE` / `SUBSET Server` placeholder — that silently weakens or strengthens the attack and produces unreliable counterexamples. Either implement the dependency faithfully or drop the category.

---

## 7. When to Skip This File

- Target is purely crash-fault-tolerant (Raft, Multi-Paxos, primary-backup): use `distributed-analysis.md` alone.
- Target's safety argument explicitly excludes Byzantine threats: use `distributed-analysis.md` alone.
- Target uses BFT consensus for a sub-protocol but the case study is scoped to the non-BFT layer: focus on the relevant layer's threat model.

If unsure, use both files; document in the modeling brief why the BFT layer is in or out of scope.
