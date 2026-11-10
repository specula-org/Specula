# Incremental validation — V02 source `3d0faba4`

## Source-delta and generation gate

- Decision: `MODEL_CHANGE_REQUIRED`. The supplied update changes complete
  ConfState restoration, learner vote handling, and Ready/Advance ownership.
- The retained reference, MC, Trace, and harness suites were incrementally
  adapted. `Update.tla` covers both the full reference next-state relation and
  an affected-action view; `UpdateWitness.tla` binds source traces to complete
  Actions with exact post-state equality.
- The complete-restoration change fixes prior MC-1. Review of the distinct live
  snapshot path identified candidate MC-2: its membership guard omits
  `VotersOutgoing` and `LearnersNext`.

## Harness and trace gate

- The retained harness was rebased onto the current source. Eleven fresh
  scenarios passed and emitted 5,778 events. `harness/coverage.json` reports
  no unvisited event or missing required witness.
- Ten non-candidate traces passed complete source/post-state correspondence and
  all normal `Trace.cfg` invariants. The 1,575-event
  `membership-snapshots` trace completed with 1,575 distinct states and zero
  queued states (task `07e57b965bb341e294649dfeffea1bb5`).
- The 299-event `outgoing-snapshot-restore` trace matched the complete
  reference and violated only `JointSnapshotMemberAcceptance` (task
  `40bef3078c294f93b76020a5b85557c9`). With that candidate property omitted,
  strict correspondence consumed all 299 events with zero queued states and no
  error (task `c18633d6e80a4d4099f5bd6492d106d8`).

## Update reachability

Every source-backed witness consumed its complete trace queue and reached the
intended negated canary:

| Scenario | Task | State |
|---|---|---:|
| Joint entry | `6f5b97ed1345443c86b57c6e765c173d` | 195 |
| Auto-leave append | `b3a60be51ec24b91b16310841f9c524d` | 197 |
| Complete joint recovery | `69c8f8d12eaa44e7aa08be4647511a09` | 230 |
| Learner vote grant | `99dde7a6592b431c924c25992d2b0366` | 425 |
| Post-Ready output preservation | `a40e7b11d0e0457b90cd08fbd9162607` | 101 |
| Outgoing-only snapshot rejection | `11405eac0e694fd1a60a4963c047ccd5` | 299 |

These expected canary violations are positive reachability evidence, not target
property failures.

## Broad model checking

All three registered BFS checks ran for their planned 30-minute budgets. Their
frontiers remained nonempty, so the result is bounded coverage rather than an
exhaustive proof.

| Check | Task | Depth | Generated | Distinct | Queue | Result |
|---|---|---:|---:|---:|---:|---|
| Standard `MC.cfg` | `085f5b72dee2438aa2c16eabdfdc815b` | 3 | 75,208,095 | 64,900,008 | 64,882,882 | budget exit; no violation |
| Full `Update_full.cfg` | `c5b9d23c65434e049e85934f9d05bed6` | 3 | 58,940,109 | 50,743,367 | 50,727,002 | budget exit; no violation |
| Focused `Update_focused.cfg` | `3d8784b5b38f48fc96bb95b2643ae4cf` | 4 | 133,244,582 | 99,849,260 | 99,766,626 | budget exit; no violation |

## Scenario exploration and exact limits

The auto-leave BFS hunt reached its planned budget with no canary or property
violation: task `3732918fdaf745afb069fcaf7800189b`, depth 6,
125,268,902 generated / 47,934,325 distinct / 45,044,610 queued.

Five concurrently scheduled BFS hunts ended when their run-local state queues
exhausted available storage. No property or canary violation was reported
before the storage error. They remain partial coverage:

| Scenario | Task | Depth | Generated | Distinct | Queue |
|---|---|---:|---:|---:|---:|
| Joint | `c7dd2d9fedf849ff88563b78b2e05190` | 6 | 97,961,915 | 37,400,546 | 35,136,950 |
| Outgoing snapshot | `f19f944c288b4be9a05d01071fb078b2` | 4 | 182,246,026 | 135,266,330 | 135,158,442 |
| Learner vote | `c4da93ac02394d039e17bd8c064ed5fc` | 6 | 129,909,314 | 52,090,145 | 49,167,876 |
| Recovery | `03c52db94327477cb0608f4db45e5c16` | 5 | 103,065,307 | 48,128,106 | 46,417,733 |
| Ready output | `6767b8337fa54e0a9fe60ba3e2968e00` | 17 | 133,739,729 | 13,314,072 | 5,275,912 |

A follow-up diagnostic confirmed that TLC's `-depth` option bounds trace
length rather than the BFS frontier. The five diagnostic replacements were
therefore stopped before repeating the storage failure and were drained through
the registered wait path; they are not campaign results.

Six independent depth-100 simulations reached their planned 30-minute budgets
without a canary, target-property, or runtime violation:

| Scenario | Task | States checked | Traces generated |
|---|---|---:|---:|
| Joint | `d08beab712ff4876812566fe66679067` | 90,889,400 | 1,267,069 |
| Outgoing snapshot | `720fa3a33b6741eba3ecbe548e52649d` | 72,382,813 | 91,264 |
| Learner vote | `66d60a2183034ea882da92a89ef84455` | 123,487,108 | 312,425 |
| Recovery | `52c904104b3f459dafd516efa3a3dbab` | 61,923,185 | 996,322 |
| Ready output | `9917b08205bf49e4a543b09778acd650` | 170,802,635 | 993,555 |
| Auto-leave | `8a1df30048c44474bfa32560f76e26f9` | 88,393,569 | 1,215,353 |

Random simulation did not itself establish the deep scenario canaries; the
complete source-backed witnesses above provide the reachability evidence.

## Confirmation and persistent findings

- MC-2 is reproduced through the public RawNode protocol interface. Three valid
  index-5 joint recovery snapshots were rejected and the response remained at
  index 4. The supplied old-source control behaves identically, so MC-2 is
  pre-existing. Evidence: `repro/MC-2/confirmation.md`; durable record:
  `spec/persistent-findings/MC-2.json`.
- The fresh MC-1 control restores all four joint progress members and does not
  elect with only the incoming majority, so prior MC-1 is fixed by this update.
- The fresh CR-3 public Node control still commits the second membership change
  before the first is applied, so prior CR-3 remains reproduced.
- Retained persistent dispositions for CR-1, CR-2, CR-4, CR-5, and CR-6 remain
  applicable because their tracked dependencies were unchanged.

## Final checks

- SANY accepts the final base, MC, Trace, Update, UpdateWitness, and retained
  quality modules.
- Instrumentation was removed cleanly. `go test -count=1 ./...` passed on the
  uninstrumented source; log: `harness/logs/final-clean-tests.log`.
- The complete classifications and validation limits are recorded in
  `confirmed-bugs.md`, `bug-severity.md`, and
  `spec/remaining-validation-work.md`.

