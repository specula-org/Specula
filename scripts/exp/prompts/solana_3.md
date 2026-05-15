## Target: Solana Tower BFT — Rust

`anza-xyz/agave` (the active maintained Solana validator client, forked from `solana-labs/solana`). Production blockchain consensus for Solana mainnet. **Tower BFT** is a fundamentally different consensus paradigm from the leader-based BFT (Tendermint, HotStuff) and DAG-BFT (Mysticeti, Bullshark) families already in our corpus: there are no traditional quorum certificates; safety is enforced by each validator's per-vote **lockout period** (exponentially growing) plus a 2/3 stake-weighted optimistic confirmation threshold.

System category: **Category A (distributed)** with a Byzantine threat model. Distinct sub-category: **vote-lockout BFT** (PoH-ordered slots + validator towers).

### Scope (important — agave is a large repository)

Focus on the Tower BFT consensus subsystem only. Skip everything else:
- Move/Sealevel VM and program runtime
- Account / state storage
- Gossip / turbine block propagation (treat as fair network model)
- RPC / JSON-RPC / banking stage / SVM / transaction processing
- Validator key management / staking program internals
- PoH service (treat as oracle producing a totally ordered slot sequence)

Search within `core/src/` for: `consensus.rs`, `tower_storage.rs`, `replay_stage.rs`, `voting_service.rs`, `vote_simulator.rs`, `cluster_slots*.rs`, and any module containing `Tower`, `Lockout`, or `switching threshold`. The brief should explicitly enumerate which files are in scope after the agent reads the repo layout.

### Production context

Solana mainnet has run Tower BFT since 2020. Known historical issues include the September 2021 outage (transaction-flood-triggered fork divergence; not a pure consensus bug but exposed Tower BFT edge cases) and ongoing discussions about optimistic-confirmation safety bounds. Anza recently rewrote significant portions of the consensus code path; the lockout / switching-threshold logic in `core/src/consensus.rs` and the tower-restore logic in `core/src/tower_storage.rs` are the most-modified safety-critical files.

### Open questions to investigate

Tower BFT's safety argument differs from quorum-cert protocols, so the open questions are protocol-specific:

1. **Lockout violation under Byzantine voting**: a Byzantine validator votes at slot S with lockout L on fork A, then attempts to vote on a different fork B at slot S+k for k < L. The protocol's design forbids this (and a slashing condition should detect it). Are there code paths where the lockout-check is bypassed — e.g., during tower-restore after crash, or during a vote replay across forks?
2. **Tower restore after crash**: `core/src/tower_storage.rs` reconstructs the validator's lockout tower from persisted state on restart. If the persisted tower disagrees with the local replay state (e.g., persisted slot is not in local DAG), what does the protocol do? Can this divergence be exploited by a Byzantine peer feeding crafted blocks?
3. **Switching threshold attack**: Tower BFT allows a validator to switch forks if the alternate fork has accumulated more than 38% (configurable) of stake-weighted votes since the validator's last vote. Can a Byzantine subset craft a slot sequence + vote pattern that lets a victim validator switch forks in a way that violates a previously committed slot's safety guarantee?
4. **Optimistic confirmation rollback**: a slot reaches optimistic confirmation (2/3 stake) but is later rolled back. The protocol claims this is unsafe-but-bounded. What is the exact bound? Can a Byzantine subset of >1/3 stake (but <2/3) drive optimistic confirmation followed by rollback?
5. **Vote replay across validators**: votes are gossiped between validators. Can a Byzantine validator replay another (honest) validator's vote on a different fork to bias optimistic-confirmation accounting?
6. **Tower equivocation**: can a Byzantine validator publish two distinct towers (different lockout sequences) to different peers, creating divergent views of who is locked-out on what?

### Out of scope

PoH / clock skew (assume validators agree on slot ordering once PoH samples are received), transaction execution, smart-contract logic, RPC. The TLA+ spec should treat slots as opaque ordered integers and stake weights as constants. Cryptographic signatures are unforgeable (no honest-signature spoofing).

### Caveat about repository state

The Anza fork is actively reorganizing the consensus code. Some of the file names and module paths above may differ from the current `main` branch. The agent's Phase 1 reconnaissance should reconcile this and record the canonical paths in the modeling brief before further phases.
