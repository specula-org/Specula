# Chapter 3: Update-Focused Deep Analysis

Perform this analysis after Chapter 2 has produced a code-faithful first draft of the new reference suite. Use the explicit changed state, Actions, assumptions, and atomicity boundaries to find interactions and properties that were not obvious from the source diff alone.

## 1. Trace the Changed Behavior Through the Old System

Ask:

- Which unchanged Actions establish each changed Action's preconditions?
- Which unchanged Actions read, overwrite, persist, send, retry, cancel, or recover the changed result?
- What happens with in-flight old messages, requests, or tasks across the changed path?
- Which faults or interleavings cross a changed atomicity boundary?
- Did the code update the same mechanism at every special/general call site and branch?
- Which old assumptions, masks, and environment constraints still hold?

Use the Category A/B analysis patterns from the installed Specula **code-analysis** skill for the changed mechanism. Do not apply an unrelated generic fault checklist.

## 2. Derive Update Scenarios

Group Scenarios by mechanism and interaction, not by changed file. Prioritize paths of these forms when supported by the code:

```text
old producer -> changed Action -> old consumer
old context -> changed Action -> crash/recovery
old Action -> changed Action -> old Action
changed Action -> changed Action
changed Action -> retry/timeout/configuration change
```

Each Scenario must identify real code paths, the model Actions needed to exercise them, the uncertainty to resolve, and a plausible correctness consequence.

Derive expectations from implementation behavior and system guarantees, then use them to challenge the draft. Include relevant boundaries where a behavior must be rejected, delayed, or become ineffective, as well as paths where it should occur. Recheck reused assumptions when a Scenario depends on them; a path admitted by the model is not by itself evidence of implementation reachability.

Use [Chapter 5's two-way behavioral review](05-completeness-review.md#2-close-the-reference-semantics) to look for missing implementation paths and unsupported model paths. Turn consequential uncertainties into Scenarios for later trace validation or model checking, with expected outcomes justified from the source rather than the draft's assignments. A successful trace replay shows that observed behavior is admitted; it does not rule out extra model behavior. Check that the selected properties can expose wrong interactions, rather than relying only on properties that restate the draft's assumptions.

## 3. Derive Properties

Classify properties as:

- preserved old properties whose justification must be rechecked;
- revised properties such as `Inv_new` when the system's guarantee changed or evidence shows the old formulation was incorrect;
- newly introduced safety/liveness properties;
- interaction properties that observe the changed behavior through an old consumer;
- structural properties needed to keep focused checking meaningful.

Do not weaken a still-promised property merely because the draft violates it. The later validation phase decides whether a violation is a model issue, property issue, or implementation bug.

## 4. Reuse Finding Lineage

For relevant prior findings, re-read the evidence rather than only the status label:

- `REPRODUCED`: can the mechanism regress or move to a sibling path?
- `MASKED`: did the update weaken/remove the mask?
- `ENV_LIMITED`: did the trigger become executable here?
- `FALSE POSITIVE` or repaired: did the reachability/property premise change?

Use closed historical bugs as mechanism evidence, not as a goal to rediscover unchanged.

## 5. Revise the Reference and Analysis

Update the reference suite whenever this analysis reveals missing state, callers, atomicity, Trace fields, MC wrappers, or setup. Update the modeling brief/report with the final evidence-backed Scenarios, modeling recommendations, exclusions, and proposed properties.

Repeat Chapters 2 and 3 until the reference expresses the analyzed behavior cleanly enough to generate `Update.tla` without duplicating semantics.
