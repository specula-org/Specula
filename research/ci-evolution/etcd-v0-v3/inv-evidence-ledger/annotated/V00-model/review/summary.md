# Review summary

- Blocks reviewed: **34**. All are in `base.tla`, the only module. There is no `Update.tla`.
- Blocks kept: **18**. Each got `review: ok`; the only edit was adding the missing `->` suffixes.
- Blocks changed: **16**.
  - Intent changed: **11**. VoteDecisionEligibility, CampaignDecisionEligibility, TransferDecisionEligibility, RequestCorrelatedConfigurationEffects, ProposalConfigurationDecisions, QuorumAccounting, AckPreservation_LogUnchanged, QuotaIntegrity, OutcomeSoundness, ReadBasis, NoUnexpectedFatal.
  - Status changed: **3**.
  - Evidence type changed: **9** lines in **8** blocks. All of them were narrating comments retyped from `comment` to `impl`: raft.go:892, raft.go:683, raft.go:751, raft.go:1412, raft.go:969 (x2), log_unstable.go:83, rawnode.go:52, raft.go:1000.
  - Evidence removed: **7** lines (README.md:124, history 516891c49, README.md:170 in OutcomeSoundness, read_only.go:20, storage.go:214, raft.go:665, history a90ffa34e).
  - Evidence re-quoted: **2** (README.md:170 in ProposalConfigurationDecisions, history f9382a4d7).
  - Evidence added: **3** (node.go:77 in PromiseBacking; history db2dbe524 in ProposalConfigurationDecisions and in OutcomeSoundness).
- New splits: **0**. No mixed property has the splittable shape: they are single `LET` contracts, or their clauses are nested under an inner `\A`.
- New `clause` lines: **+14** (35 -> 49), in 8 blocks. Clause lines in 3 more blocks were rewritten.

## Status matrix (old -> new)

| old \ new | requirement | impl-abstraction | unknown | model-internal | total old |
|---|---|---|---|---|---|
| requirement | 26 | 0 | 0 | 0 | 26 |
| impl-abstraction | **2** | 0 | 0 | 0 | 2 |
| unknown | **1** | 0 | 1 | 0 | 2 |
| model-internal | 0 | 0 | 0 | 4 | 4 |
| total new | 29 | 0 | 1 | 4 | 34 |

All three status changes come from the TASK's preferred fix: narrow the intent to the evidence-backed part, give it status `requirement`, and record the code-only remainder in `clause` lines (impl-abstraction or unknown). The three blocks are ProposalConfigurationDecisions, OutcomeSoundness and NoUnexpectedFatal.

## Five blocks I was least sure about

1. **OutcomeSoundness / ProposalConfigurationDecisions** (impl-abstraction -> requirement). The formulas check one exact decision, and the code-only precedence and "Accepted otherwise" make up much of that check. Narrowing follows the rule as written, but keeping `impl-abstraction` with clause lines is also defensible.
2. **NoUnexpectedFatal** (unknown -> requirement). Same narrowing argument. Only 4 of the 15 modelled fatal reasons have a documented forbidden trigger, and the "append/conflict below committed" clause rests on the Raft paper rather than on a code comment.
3. **AckPreservation_LogUnchanged**. The formula checks full log equality across Advance. ee0757a9b supports only "do not mark truncated entries stable". I narrowed the intent; downgrading the whole block to `impl-abstraction` would also be defensible.
4. **VoteDecisionEligibility**. Retyping raft.go:892 ("We can vote if this is a repeat of a vote...") as narration is a judgement call. By contrast, I kept log.go:200 "never decrease commit" (CommittedHistory) as a rule-stating `comment`.
5. **QuotaIntegrity**. Whether "monotonic sequence of indexes" / "MUST be added into inflights in order" already implies strictly increasing indexes. If it does, the strictness clause is a requirement and the old intent was correct.

## Checks

- SANY: `spec-reviewed/base.tla` parses with no errors.
- `diff -ru spec-annotated spec-reviewed`: 422 changed lines, all of them comment lines. No non-comment line changed, and no `.cfg` changed.
- All 34 blocks have exactly one `review:` line, every quote is found at or near its cited line, and every kept non-`impl` evidence line has a `->` suffix.
- Some properties named in the `.cfg` files have no definition anywhere in the workspace, so they have no block: MCTypeOK, TraceMatched, ElectionProgress, CatchupProgress, ManagementProgress, TransferSettlement and ReadProgress. They belong to the MC and Trace modules, which are not here. See `check.md`.
