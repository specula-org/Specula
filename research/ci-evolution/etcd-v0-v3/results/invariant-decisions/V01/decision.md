Decision: **maintain selectively and extend coverage**. Keep the Raft safety requirements; migrate their observations to joint configurations and V2 entries. The JSON gives explicit predicates, evidence and witnesses for all 35 old properties: **21 keep, 14 modify, none remove**. It proposes **15 additions** and leaves one stronger transfer rule unresolved.

This is the independent initial assessment. Only supplied workspace material was used. No tests or TLC were executed, and no code or spec was changed.

The central representation must distinguish incoming voters, outgoing voters, active learners, staged learners and AutoLeave. Quorum requires a majority of **each** voter set; a majority of their union is insufficient. For example, incoming={1,2}, outgoing={2,3}, acknowledgements={1,2} cannot commit. Staged learners remain outgoing voters until leaving joint.

| Maintenance category | Decision |
| --- | --- |
| Unchanged requirements | Retain election uniqueness, log matching, leader completeness, committed/applied history agreement, durable vote/promise backing, replication evidence, application/read correlation, quota bounds and log structure. Retain the existing temporal targets without claiming they were checked. |
| Observer migrations | Carry both voter sets, complete V2 batches/context/version, actual learner flags, configuration provenance and Ready phases. Extend configuration classification to V2, including internal leave entries. |
| Supported semantic changes | Support voter demotion, joint entry/exit, idempotent unknown removal, explicit bootstrap, documented invalid-change rejection, observational Ready calls and quota release at Advance. |
| Old property repairs | ProposalConfigurationDecisions lacks pending-index post-state and complete content checks. OutcomeSoundness obtains its effective weight through the implementation's RewriteConf, allowing correlated mistakes. Repair these specifically. |

**The important edits are narrow.** RequestCorrelatedConfigurationEffects must permit tested demotion and require the exact atomic batch result. ConfigurationTransitionSafety still requires the predecessor quorum: entering joint commits under the old configuration; leaving commits under both joint majorities. An internal id=0 exit must not inherit the old bootstrap exemption.

AckPreservation currently requires identical log histories before and after Advance. A correct new Advance can append an automatic exit, so allow exactly one independently justified leave entry while preserving the entire previous prefix, captured applied cursor and snapshot acknowledgement protection. A generic “prefix preserved” replacement would be too weak.

ConfigurationOrigin and SnapshotBacking must preserve all configuration fields and support explicit Storage anchors without inventing bootstrap log entries. NoUnexpectedFatal should distinguish the newly tested negative API cases from unexpected failures; a duplicate internally generated exit remains unexpected.

**Existing checks already cover substantial behavior.** ProposalContract already checks pending rewrites and acceptance/rejection; its entry observer needs V2 support. VoteContract checks exact vote responses, while CampaignContract already requires pending committed configuration changes to block Hup. ReadyAccounting already checks contiguous committed pages and their actual cursor. PromiseBacking uses durable disk state, so omitted unchanged HardState does not require weaker durability. ReadBasis already uses confirmation-time configuration, including when a later read acknowledgement releases a prefix. The JSON explains each observer and its remaining limits.

**Defects must remain visible.**

- The campaign scan in new/source/raft.go:1580 counts only V1 entries. A committed, unapplied V2 entry must still block Hup.
- Snapshot/restart reconstruction reads only Nodes and Learners. It drops NodesJoint, LearnersNext and AutoLeave, and rejects an outgoing-only snapshot recipient.
- Config.Clone() omits AutoLeave. A status copy of a joint configuration can therefore misreport the flag.
- Successful automatic exit append leaves pendingConfIndex unchanged. With enter at 10 and committed normal entries through 12, successive paginated Advances can append exits 13 and 14 before the first applies.
- Automatic exit admission occurs before Advance releases quota. An initial quota rejection can leave no later cursor-bearing Advance to retry without another client write.
- Demotion leaves serving/transfer state needing scrutiny: a demoted leader can reach the singleton read shortcut, and a demoted transferee can later receive TimeoutNow. Keep read and learner safety; the requirement for immediate transfer abort remains unresolved.

Other recorded concerns include a latent nil-error branch in Changer.Simple, StartNode ignoring Bootstrap's error, and stale joining instructions. Their certainty and validation limits are stated individually.

**Additional coverage is required.** The additions cover configuration validation and progress preservation, commit reevaluation, automatic-exit serialization/progress, complete snapshot restoration, Ready purity/deltas/quota timing, explicit bootstrap, faithful independent status copies, encoding, CheckQuorum decisions, read issuance and Node proposal-channel removal.

The old workload cannot express V2 batches, outgoing voters, staged learners or automatic exit. The new single-node configuration test explicitly applies an exit without committing it; it establishes transformation expectations, not joint-quorum safety or completion.

Validation must also resolve RawNode's handling contract: its comment forbids state-changing calls while a Ready is handled, but its tests require ApplyConfChange before Advance. Do not ban necessary callbacks or apply RawNode restrictions to Node's asynchronous loop to eliminate failures.

The JSON includes concrete comparison witnesses and unchanged safety controls. Passing the old flat model alone would leave the new obligations unassessed.
