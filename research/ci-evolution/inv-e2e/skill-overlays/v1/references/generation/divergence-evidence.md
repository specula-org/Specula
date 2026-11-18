# Divergence Evidence for Property Decisions

An update can make an old property wrong in two directions. If the update legitimately allows states the old property forbids, the old property raises false alarms. If the update forbids states the old property allows, the old property still passes but no longer catches a regression to the old behavior. A property decision (keep, modify, add, remove) is therefore a claim about specific states, and it needs the same kind of evidence as a model edit: a concrete state on which the decision makes a difference, evaluated on the actual TLA+ definitions, and checked against what the system should allow.

This chapter applies wherever properties are decided: Chapter 3 §3 (Derive Properties), Chapter 4 §5 (Update-Specific Properties), and Chapter 5 (completeness). It does not replace them; it defines the evidence they require. It also applies to `NO_MODEL_CHANGE` runs that repair or keep properties whose observed state the update touches.

## 1. Which Properties Need a Decision

A property is **affected** when the update changes any Action, helper, observer, history/quality record, variable meaning, or configuration that the property reads, or when the update introduces a new instance of a concept the property quantifies over (for example a new entry, message, or configuration kind that the property's predicate does not mention).

The second case catches omissions. A diff shows what changed, not what should have changed and did not. When the update adds a new kind of thing, search for every property and every code site that handles the old kinds, and decide whether the new kind must be covered.

Every affected property gets an explicit decision: `keep`, `modify`, `add`, `remove`, or `unresolved`. Unaffected properties keep their status and are not re-argued. Keep at least one unaffected core safety property enabled in the update checks as a control, so that an accidental global weakening is visible.

## 2. The Separating State

For each `modify`, `add`, or `remove`, give a **separating state**: a concrete assignment to the spec's variables (or a transition, for action properties) on which the old and the proposed property give different verdicts.

- **Weakening** (the new property accepts more): a state the new model can produce, which the old property rejects and the new property accepts.
- **Strengthening** (the new property accepts less): a state the old model could produce, which the old property accepts and the new property rejects. Keep newly forbidden old behavior in the comparison; do not restrict the domain to states the new implementation reaches, or the strengthening becomes untestable.
- **Semantic replacement:** one state of each kind if the change both admits and forbids.
- **Representation-only change** (observer or field migration with the same meaning): one state with nonempty relevant records on which both properties agree, mapped across the representation change.

For an added property with no old counterpart, the old verdict is "not checked"; give a state the new property rejects and explain why the system must not reach it.

**Non-vacuity.** Many properties quantify over histories, message sets, or quality records. A state whose relevant records are empty separates nothing. Populate the records from a real mapped pre/post state and inputs, and say where they came from. If an observer lacks a field the decision depends on, migrate the observer first and evidence that migration separately; do not choose a truth value by hand.

**Where the state comes from**, strongest first:

1. `trace`: a state from a validated trace on the old or new implementation, or a short edit of one;
2. `mc`: a state reached by TLC from `Init` or from a validated trace prefix, for example as the counterexample to a reachability canary;
3. `constructed`: a type-correct state built by hand.

A `constructed` state is acceptable for the first judgment. Before final reporting, upgrade every weakening witness to `trace` or `mc`, or record the decision as resting on an unreachable-in-practice state. A weakening justified only by a state the model cannot reach justifies nothing.

## 3. Evaluate the Actual Definitions

Evaluate the old and proposed properties on the separating state with TLC. Do not evaluate a Python, prose, or hand translation: identical predicate text can mean different things when a helper or observer changed.

Put evaluation files under `spec/evidence/<id>/`. Copy the prior module under a new name so that both versions can be instantiated together, for example `OldBase.tla` from the previous suite's `base.tla` (rename the `MODULE` line only):

```tla
---- MODULE E1 ----
EXTENDS TLC
CONSTANTS ...
S0 == [raft |-> ..., history |-> ...]          \* the separating state
Old == INSTANCE OldBase WITH raft <- S0.raft, history <- S0.history, ...
New == INSTANCE base    WITH raft <- S0.raft, history <- S0.history, ...
ASSUME PrintT(<<"E1", Old!Prop, New!Prop_new>>)
====
```

Alternatively use a one-state spec (`Init == vars = S0`, `Next == UNCHANGED vars`) with the property as an invariant. Either form evaluates one fixed state; it is a static preflight, not a model-checking campaign, and is permitted during Generation. Record the command, the log path, and both truth values.

## 4. Controls

A relaxation can silently erase detection; a strengthening can silently reject legal behavior. For each edit, evaluate one control state near the separating state:

- **Weakening:** a nearby state that must still be forbidden (for example the same append without the condition that legitimises it). The proposed property must still reject it.
- **Strengthening:** a nearby legal state. The proposed property must still accept it.

If the control fails, the edit is too broad or too narrow; revise it.

## 5. Two Questions, Answered Separately

For each separating state, record two judgments. Never derive one from the other.

**Does the implementation produce it?** (`impl_produces`: `yes` / `no` / `unknown`). Answer from a code observation (§6) when possible, otherwise from cited code paths.

**Should the system allow it?** (`requirement`: `allowed` / `forbidden` / `unknown`). Valid requirement evidence is only:

- test assertions and test data;
- documentation and design text;
- API, protocol-buffer, and interface contract comments;
- source comments that state an intent, rule, contract, or reason ("must", "never", "so that", "it is an error to");
- the protocol the system implements, cited by section;
- commit messages or removed comments, when history is available.

Implementation code is never requirement evidence; the code being written that way is exactly what is under test. A comment that only narrates the next lines ("retry now", "bump the counter") is implementation evidence. Cite every piece as `path:line`.

Then act on the combination:

| | allowed | forbidden |
|---|---|---|
| **implementation produces it** | weakening justified | **bug candidate**: keep the stronger property, record the defect, do not edit the property to accept the state |
| **implementation does not produce it** | the edit may be unnecessary; if kept, the control from §4 must show detection is not lost | strengthening justified |
| **either is unknown** | `unresolved`: do not edit toward the implementation's behavior; state what evidence would settle it | `unresolved` |

The bug-candidate cell is the default whenever the only reason to accept a state is that the new code produces it. Overriding it requires non-implementation evidence that the state is allowed. Submit every bug candidate to Part 4 through the normal code-review candidate path; a property edit is never the place to resolve it.

## 6. Code Observation

Where a separating state concerns implementation behavior, drive the real code to the corresponding pre-state and record what it does. Prefer, in order: an existing test or test helper; the update-focused scenarios of Validation 2; a small new test in the writable source copy. Run old and new code when the question is whether the update changed the behavior.

Code observation runs in Validation, not Generation. Record the first judgment in Generation from source reading, then complete the observation when the harness is available and revise the decision if the observation contradicts it. Record `not_representable` or `unknown` rather than inventing a result.

## 7. Keeping Needs Evidence Too

"No change needed" is a decision, not a default. For every affected property you keep:

1. take at least one state that the new implementation produces in the changed behavior (prefer `trace` or `mc`), with the property's records nonempty;
2. evaluate the old property on it with TLC;
3. answer the requirement question for that state.

The kept property must give the verdict the requirement demands. If the new behavior is legal and the old property rejects it, or the new behavior is forbidden and the old property accepts it, the decision is wrong; change it. In particular, an exact-equality or "never changes X" clause that described the old implementation must be checked against every new way the update lets X change.

## 8. Budget

Evidence is for decisions, not for coverage. Prioritise update-related semantic edits, then kept properties whose observed state the update touches, then representation changes. Stop adding states once each decision has one separating (or keep) state and one control. Do not run exploration campaigns for evidence; reuse states from trace validation and model checking when they arrive.

## 9. Record

Write `spec/invariant-evidence.json`. It is an evidence record for review and for later runs, not a change contract between chapters. Keep one entry per affected property and one record per evaluated state:

```json
{
  "entries": [
    {
      "property": "Prop_new",
      "replaces": "Prop",
      "decision": "modify",
      "kind": "weakening",
      "affected_because": "Advance may now append an entry (raft.go:advance)",
      "initial_decision": "modify",
      "changed_from_initial": false,
      "evidence_ids": ["E1", "E1c"]
    }
  ],
  "evidence": [
    {
      "id": "E1",
      "property": "Prop_new",
      "role": "separating",
      "state_source": "trace",
      "state": "spec/evidence/E1/E1.tla",
      "how_populated": "post-state of event 153 in traces/joint.ndjson",
      "old": {"claimed": false, "tlc": false},
      "new": {"claimed": true, "tlc": true},
      "log": "spec/evidence/E1/tlc.log",
      "impl_produces": {"value": "yes", "basis": "TestAutoLeave in evidence/E1/"},
      "requirement": {"value": "allowed", "citations": ["raftpb/raft.proto:112"]},
      "cell": "weakening justified"
    },
    {
      "id": "E1c",
      "property": "Prop_new",
      "role": "control",
      "state_source": "constructed",
      "state": "spec/evidence/E1c/E1c.tla",
      "expected": false,
      "new": {"claimed": false, "tlc": false},
      "log": "spec/evidence/E1c/tlc.log"
    }
  ],
  "bug_candidates": ["E7"],
  "unresolved": [{"property": "...", "missing_evidence": "..."}]
}
```

`initial_decision` is the decision made from source reading before any code observation; keep it unchanged afterwards so that reviewers can see what the evidence changed.

## 10. Completion

Chapter 5 is not complete while:

- an affected property has no decision;
- a `modify`, `add`, or `remove` has no separating state evaluated by TLC, or its claimed and TLC truth values disagree;
- a weakening rests only on a `constructed` state without a recorded limitation;
- an affected `keep` has no evidence state;
- a bug candidate was resolved by editing the property;
- a property is credited by a state whose relevant records are empty.

Report unresolved entries in the final result as coverage limits, not as passes.
