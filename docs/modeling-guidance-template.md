# Target-Specific Modeling Guidance

## Objective

- [Describe the behavior, risk, or subsystem this run should prioritize.]

## Required Scope

- `[path/to/file:line or symbol]`: [Explain why this code must be analyzed.]
- [List the other modules or entry points that belong in scope.]

## Required Coverage

- [Describe an important interaction or call path that must be followed.]
- [Identify the normal, failure, recovery, concurrency, or ordering behavior that must be considered.]

## Scenario Hypotheses

- Can [event or interleaving] cause [undesired outcome]?
- What happens when [failure or recovery event] occurs while [operation] is in progress?
- Does [component or code path] preserve [expected behavior] across [state transition]?

## Known Incidents and References

- [Issue, pull request, incident, paper, or design document]: [Briefly explain why it matters.]

## Out of Scope

- [Subsystem or behavior]: [Explain why it should be excluded.]
